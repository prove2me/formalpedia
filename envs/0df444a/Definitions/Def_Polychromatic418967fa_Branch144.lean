-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch144
-- name    : Polychromatic418967fa_Branch144
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:16:01.236692+00:00
-- url     : https://prove2.me/theorems/4a4577c9-36cb-445e-b721-1a3e5bf6e681
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

def Polychromatic418967fa.branch_144 : allB 144 144 :=
  allB_succ' 2 143 144 (Eq.refl Bool.true) (allA_succ_of_accept 1 143 144 (accept_3_4 1 143 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 144)) (allB_succ' 3 142 144 (Eq.refl Bool.true) (allA_succ_of_gcd 2 142 144 2 1 71
  72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 144
  (Polychromatic418967fa.accept_15_1_7_9_1_20 1 142 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 142 144))) (allB_succ' 4 141 144 (Eq.refl Bool.true) (allA_succ_of_gcd 3 141 144 3 1 47 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 144
  (Polychromatic418967fa.accept_19_2_8_11_1_7701 2 141 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 1 141 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 144)))) (allB_succ' 5 140 144 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  140 144 4 1 35 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 140 144 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 140 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 140 144 2 1 70 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 140 144 (accept_3_4 1 140 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  144))))) (allB_succ' 6 139 144 (Eq.refl Bool.true) (allA_succ_of_accept 5 139 144 (accept_3_5 5 139 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 144 (Polychromatic418967fa.accept_21_4_13_18_1_137 4 139
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 139 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 144 (accept_3_5 2 139 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 144 (Polychromatic418967fa.accept_19_1_6_11_1_7548 1 139 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 144)))))) (allB_succ' 7 138 144 (Eq.refl Bool.true) (allA_succ_of_gcd 6 138 144 6 1 23 24
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 144
  (Polychromatic418967fa.accept_11_5_6_1_1_988 5 138 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 138 144 2 2 69 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 138 144 3 1 46 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 138 144 2 1 69 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 138 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 138 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138 144))))))) (allB_succ' 8 137 144 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 137 144 (accept_3_4 7 137 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 137 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 144 (Polychromatic418967fa.accept_21_5_11_18_1_1789 5 137 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 144 (accept_3_4 4 137 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 137 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 144
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 137 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 144 (accept_3_4 1 137 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  144)))))))) (allB_succ' 9 136 144 (Eq.refl Bool.true) (allA_succ_of_gcd 8 136 144 8 1 17 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 144
  (Polychromatic418967fa.accept_13_7_6_1_1_368 7 136 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 144 2 3 68 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 144 (accept_3_5 5 136 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  144 4 1 34 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 144 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 136 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 144 2 1 68 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 136 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 136 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 144))))))))) (allB_succ' 10 135 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 135 144 9 1 15 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 144 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 135 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 144 (Polychromatic418967fa.accept_17_7_16_8_1_7613 7 135
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 144 3 2 45 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 135 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 144 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 135 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 144 3 1 45 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 135 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 144
  (Polychromatic418967fa.accept_10_1_5_4_1_276 1 135 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135 144)))))))))) (allB_succ' 11 134 144 (Eq.refl Bool.true) (allA_succ_of_gcd 10 134 144 2 5 67 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 144
  (Polychromatic418967fa.accept_19_9_1_11_1_7643 9 134 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 144 2 4 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 144 (accept_3_4 7 134 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  144 2 3 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 134 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 144 2 2 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 134 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 134 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 144 2 1 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 144 (accept_3_4 1 134 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134 144))))))))))) (allB_succ' 12 133 144 (Eq.refl Bool.true) (allA_succ_of_accept 11
  133 144 (accept_3_5 11 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 144
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 133 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 133 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 144 (accept_3_5 8 133 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 133 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 133 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 144 (Polychromatic418967fa.accept_13_6_3_1_1_1413
  6 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 144 (accept_3_5 5
  133 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 144
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 133 144 (Polychromatic418967fa.accept_14_3_7_4_1_118 3 133 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 144 (accept_3_5 2 133 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 133 144 (Polychromatic418967fa.accept_23_1_18_6_1_7716 1 133 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 144)))))))))))) (allB_succ' 13 132 144 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 132 144 12 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 132 144 (Polychromatic418967fa.accept_21_11_6_18_1_4450 11 132 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 144 2 5 66 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 132 144 3 3 44 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 132 144 4 2 33 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 144
  (Polychromatic418967fa.accept_10_7_2_4_1_569 7 132 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 144 6 1 22 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 132 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 144 4 1 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 144 3 1 44 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 144 2 1 66 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 144 (Polychromatic418967fa.accept_19_1_18_11_1_4704 1 132
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 144))))))))))))) (allB_succ' 14 131 144
  (Eq.refl Bool.true) (allA_succ_of_accept 13 131 144 (accept_3_4 13 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 144 (Polychromatic418967fa.accept_21_12_5_18_1_7715 12 131 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 144
  (Polychromatic418967fa.accept_21_11_5_18_1_5998 11 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 131 144 (accept_3_4 10 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 131 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 131 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 131 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 144 (accept_3_4 7 131 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 6
  131 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 144
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 144 (accept_3_4 4 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 144 (Polychromatic418967fa.accept_17_3_12_8_1_1688 3 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 131 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 144 (accept_3_4 1 131 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 144)))))))))))))) (allB_succ' 15 130 144 (Eq.refl Bool.true) (allA_succ_of_gcd 14
  130 144 2 7 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  13 130 144 (Polychromatic418967fa.accept_19_13_16_11_1_6047 13 130 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 144 2 6 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 144 (accept_3_5 11 130 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 130 144 2 5 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 130 144 (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 130 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 130 144 2 4 65 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 130 144
  (Polychromatic418967fa.accept_21_7_4_18_1_4471 7 130 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 130 144 2 3 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 130 144 (accept_3_5 5 130 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 130
  144 2 2 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  130 144 (Polychromatic418967fa.accept_15_3_10_9_1_769 3 130 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 130 144 2 1 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 130 144 (Polychromatic418967fa.accept_15_1_10_9_1_1495 1 130 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130 144))))))))))))))) (allB_succ' 16 129 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 129 144 3 5 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 144 (Polychromatic418967fa.accept_19_14_15_11_1_4739 14 129 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 144 (Polychromatic418967fa.accept_7_6_3_4_1_294
  13 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 144 3 4 43 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 144
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 129 144 (Polychromatic418967fa.accept_19_10_15_11_1_3421 10 129 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 144 3 3 43 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 144 (Polychromatic418967fa.accept_14_7_3_4_1_1816 7 129 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 144 3 2 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 129 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 144
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 144 3 1 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 144 (Polychromatic418967fa.accept_13_2_12_1_1_343 2 129 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 129 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129 144)))))))))))))))) (allB_succ' 17 128 144
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 128 144 16 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 128 144 (Polychromatic418967fa.accept_19_15_14_11_1_7682 15 128 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 144 2 7 64 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 144 (accept_3_4 13
  128 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 144 4 3 32 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 144
  (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 128 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 144 2 5 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 128 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 144 8 1 16 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 144 (accept_3_4 7 128 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 144 2 3 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 128 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 144 4 1 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 144 (Polychromatic418967fa.accept_13_3_11_1_1_2122
  3 128 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 144 2 1 64 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 144 (accept_3_4 1
  128 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128 144))))))))))))))))) (allB_succ' 18 127 144 (Eq.refl
  Bool.true) (allA_succ_of_accept 17 127 144 (accept_3_5 17 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 127 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 144 (Polychromatic418967fa.accept_21_15_1_18_1_3066 15 127
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 144 (accept_3_5 14 127
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 13 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 127 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 144 (accept_3_5 11 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 127 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 127 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 144 (Polychromatic418967fa.accept_13_9_10_1_1_1389
  9 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 144 (accept_3_5 8
  127 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 144
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 127 144 (Polychromatic418967fa.accept_19_6_13_11_1_7495 6 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 144 (accept_3_5 5 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 127 144 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 127 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 144 (accept_3_5 2 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 144)))))))))))))))))) (allB_succ' 19 126 144 (Eq.refl Bool.true) (allA_succ_of_gcd 18 126
  144 18 1 7 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  126 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 126 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 126 144 2 8 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 144 3 5 42 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 144 2 7 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 126 144 (Polychromatic418967fa.accept_19_13_12_11_1_1249 13 126 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 144 6 2 21 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 144
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 126 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 144 2 5 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 126 144 9 1 14 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 126 144 2 4 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 144 (Polychromatic418967fa.accept_19_7_12_11_1_7621 7 126 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 144 6 1 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 126 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 144 2 2 63 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 144 3 1 42 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 144 2 1 63 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 144
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 126 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 144))))))))))))))))))) (allB_succ' 20 125 144 (Eq.refl Bool.true) (allA_succ_of_accept 19 125 144
  (accept_3_4 19 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 144
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 125 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 125 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 144 (accept_3_4 16 125 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 125 144 (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 125 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 144
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 144 (accept_3_4 13 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 125 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 144 (accept_3_4 10 125 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 125 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 144
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 144 (accept_3_4 7 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 125 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 144 (accept_3_4 4 125 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 125 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 144 (accept_3_4 1 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  144)))))))))))))))))))) (allB_succ' 21 124 144 (Eq.refl Bool.true) (allA_succ_of_gcd 20 124 144 4 5 31 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 144
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 144 2 9 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 144 (accept_3_5 17 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 144 4 4 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 144 2 7 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 124 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 144 4 3 31 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 144 (accept_3_5 11 124 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 144 2 5 62 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 144 4 2 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 144 (Polychromatic418967fa.accept_21_7_19_18_1_7540 7 124 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 144 2 3 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 144 (accept_3_5 5 124 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 144 4 1 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 144 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 124 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 144 2 1 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1
  124 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124 144)))))))))))))))))))))
  (allB_succ' 22 123 144 (Eq.refl Bool.true) (allA_succ_of_gcd 21 123 144 3 7 41 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 144
  (Polychromatic418967fa.accept_13_7_6_1_1_368 20 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 144 3 6 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 144 (Polychromatic418967fa.accept_10_7_3_4_1_978
  17 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 144
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 16 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 144 3 5 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 144 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 123
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 144 3 4 41 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 144
  (Polychromatic418967fa.accept_27_11_15_9_1_7714 11 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 123 144 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 123 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 144 3 3 41 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 144
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 144 3 2 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 144 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 123 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 144
  (Polychromatic418967fa.accept_22_4_13_12_1_2830 4 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 144 3 1 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 144 (Polychromatic418967fa.accept_14_1_11_4_1_3430 1 123
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123 144)))))))))))))))))))))) (allB_succ'
  23 122 144 (Eq.refl Bool.true) (allA_succ_of_gcd 22 122 144 2 11 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 144 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  21 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 122 144 2 10 61 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 122 144
  (accept_3_4 19 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 122 144 2 9 61 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 122 144
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 122 144 2 8 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 122 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 122 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 144 2 7 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 144 (accept_3_4 13 122 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 144 2 6 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 144 (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 122
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 122 144 2 5 61 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 122 144
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 122 144 2 4 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 122 144 (accept_3_4 7 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 122
  144 2 3 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  122 144 (Polychromatic418967fa.accept_17_5_3_8_1_1697 5 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 122 144 2 2 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 122 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 122 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 144 2 1 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 144 (accept_3_4 1 122 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 122 144))))))))))))))))))))))) (allB_succ' 24 121 144 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 121 144 (accept_3_5 23 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 144 (Polychromatic418967fa.accept_15_7_1_9_1_1500 22 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 144 (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 121 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 144 (accept_3_5 20 121 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 121 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 144
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 144 (accept_3_5 17 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 144 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 121 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 144 (accept_3_5 14 121 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 121 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 144 (accept_3_5 11 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 144 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 144 (Polychromatic418967fa.accept_19_9_7_11_1_7602 9 121 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 144 (accept_3_5 8 121 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 121 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 144 (accept_3_5 5 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 144 (Polychromatic418967fa.accept_19_4_7_11_1_6056 4 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 144 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 121 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 144 (accept_3_5 2 121 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 144 (Polychromatic418967fa.accept_22_1_11_12_1_7713 1 121 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121 144)))))))))))))))))))))))) (allB_succ' 25 120 144
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 144 24 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 120 144 (Polychromatic418967fa.accept_21_2_15_18_1_806 23 120 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 144 2 11 60 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 144 3 7 40 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 144 4 5 30 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 19 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 144 6 3 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 120 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 144 8 2 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 144 3 5 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 144 2 7 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017
  13 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 144 12 1 10 12
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 144
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 144 2 5 60 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 120 144 3 3 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 120 144 8 1 15 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 120 144 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 120 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 144 6 1 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 120 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 144 4 1 30 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 144 3 1 40 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 144 2 1 60 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 144
  (Polychromatic418967fa.accept_19_1_6_11_1_7548 1 120 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 120 144))))))))))))))))))))))))) (allB_succ' 26 119 144 (Eq.refl Bool.true) (allA_succ_of_accept 25 119 144
  (accept_3_4 25 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 119 144
  (Polychromatic418967fa.accept_14_10_7_4_1_3453 24 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 119 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 144 (accept_3_4 22 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 119 144 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 119 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 144
  (Polychromatic418967fa.accept_15_5_14_9_1_274 20 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 144 (accept_3_4 19 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 144 (Polychromatic418967fa.accept_14_3_7_4_1_118 17 119 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 144 (accept_3_4 16 119 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 119
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 144
  (Polychromatic418967fa.accept_19_14_5_11_1_7712 14 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 119 144 (accept_3_4 13 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 119 144 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 144 (Polychromatic418967fa.accept_14_11_7_4_1_3449 11 119
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 144 (accept_3_4 10 119
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 144
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 119 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 144 (accept_3_4 7 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 119 144 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 119 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420
  5 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 144 (accept_3_4 4
  119 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 3 119 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 119 144 (Polychromatic418967fa.accept_20_2_19_4_1_3246 2 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 144 (accept_3_4 1 119 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 119 144)))))))))))))))))))))))))) (allB_succ' 27 118 144 (Eq.refl Bool.true) (allA_succ_of_gcd
  26 118 144 2 13 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 118 144 (Polychromatic418967fa.accept_21_4_13_18_1_137 25 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 118 144 2 12 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 118 144 (accept_3_5 23 118 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 118 144 2 11 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 118 144 (Polychromatic418967fa.accept_19_2_4_11_1_7507 21 118
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 144 2 10 59 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 144 2 9 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 144 (accept_3_5 17 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 144 2 8 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 144 2 7 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 144 (Polychromatic418967fa.accept_31_13_25_20_1_7711 13 118 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 144 2 6 59 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 144 (accept_3_5 11
  118 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 144 2 5 59 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 144 2 4 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 144 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 144 2 3 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 144 (accept_3_5 5 118 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 144 2 2 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 118 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 144 2 1 59 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 144 (Polychromatic418967fa.accept_22_1_8_12_1_5938
  1 118 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118 144)))))))))))))))))))))))))))
  (allB_succ' 28 117 144 (Eq.refl Bool.true) (allA_succ_of_gcd 27 117 144 9 3 13 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 144
  (Polychromatic418967fa.accept_21_5_12_18_1_7637 26 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 117 144 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 117 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 144 3 8 39 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 144 3 7 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 20
  117 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 144
  (Polychromatic418967fa.accept_15_4_12_9_1_773 19 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 144 9 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 144 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 117 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 144 3 5 39 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 144
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 117 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 144 3 4 39 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 144 (Polychromatic418967fa.accept_15_10_12_9_1_776 10 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 144 9 1 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 117 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 144
  (Polychromatic418967fa.accept_20_7_17_4_1_3239 7 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 144 3 2 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 144 (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 144 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 117 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 144 3 1 39 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 2 117 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 117 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 144)))))))))))))))))))))))))))) (allB_succ' 29 116 144 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 116 144 4 7 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 116 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 116 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 144 2 13 58 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 144 (accept_3_4 25 116 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 144 4 6 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 144 (Polychromatic418967fa.accept_17_6_14_8_1_3858
  23 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 144 2 11 58 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 144
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 144 4 5 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 144 (accept_3_4 19 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 144 2 9 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 116 144 (Polychromatic418967fa.accept_15_2_11_9_1_263 17 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 116 144 4 4 29 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 116 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 116 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 144 2 7 58 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 144 (accept_3_4 13 116 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 144 4 3 29 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 144
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 144 2 5 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 144 (Polychromatic418967fa.accept_19_9_2_11_1_7581 9 116 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 144 4 2 29 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 144 (accept_3_4 7 116 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 144 2 3 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 116 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 144 4 1 29 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 144
  (Polychromatic418967fa.accept_19_3_2_11_1_7647 3 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 144 2 1 58 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 144 (accept_3_4 1 116 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  144))))))))))))))))))))))))))))) (allB_succ' 30 115 144 (Eq.refl Bool.true) (allA_succ_of_accept 29 115 144
  (accept_3_5 29 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 144
  (Polychromatic418967fa.accept_11_6_5_1_1_586 28 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 115 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 144 (accept_3_5 26 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 115 144 (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 115 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 144
  (Polychromatic418967fa.accept_21_3_10_18_1_7631 24 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 115 144 (accept_3_5 23 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 115 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 115
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 144 (accept_3_5 20 115
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 144
  (Polychromatic418967fa.accept_10_9_5_4_1_966 19 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 144 (Polychromatic418967fa.accept_15_3_10_9_1_769 18 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 144 (accept_3_5 17 115 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 115 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 144 (accept_3_5 14 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 144 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 115 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 144 (accept_3_5 11 115 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 144 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 115
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 144
  (Polychromatic418967fa.accept_10_9_5_4_1_966 9 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 144 (accept_3_5 8 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 144 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 115 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 144 (accept_3_5 5 115 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 144 (Polychromatic418967fa.accept_15_4_10_9_1_4298 4 115 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 144
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 144 (accept_3_5 2 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 115 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 144)))))))))))))))))))))))))))))) (allB_succ' 31 114 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 114 144 6 5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 144 (Polychromatic418967fa.accept_20_9_14_4_1_4540 29 114 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 144 2 14 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 144 3 9 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 144 2 13 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 144
  (Polychromatic418967fa.accept_21_4_9_18_1_6001 25 114 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 144 6 4 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 144 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 114 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 144 2 11 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 144 3 7 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 144 2 10 57 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 114 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 144 6 3 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 144 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 114 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 144 2 8 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 144 3 5 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 144 2 7 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  114 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 144 6 2 19 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 144
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 114 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 114 144 2 5 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 144 3 3 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 144 2 4 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 114 144 (Polychromatic418967fa.accept_21_7_9_18_1_7519 7 114 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 144 6 1 19 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 114 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 114 144 2 2 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 114 144 3 1 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 114 144 2 1 57 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 144 (Polychromatic418967fa.accept_21_1_9_18_1_4428 1 114 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 114 144))))))))))))))))))))))))))))))) (allB_succ' 32 113 144 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 113 144 (accept_3_4 31 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 113 144 (Polychromatic418967fa.accept_21_9_8_18_1_7516 30 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 29 113
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 144 (accept_3_4 28 113
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 144
  (Polychromatic418967fa.accept_10_7_3_4_1_978 27 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 113 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 144 (accept_3_4 25 113 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 113 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 144
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 144 (accept_3_4 22 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 144 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 144 (Polychromatic418967fa.accept_19_1_18_11_1_4704 20 113 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 144 (accept_3_4 19 113 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 144 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 113
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 144 (accept_3_4 16 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 144 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 144 (Polychromatic418967fa.accept_15_14_8_9_1_1452 14 113 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 144 (accept_3_4 13 113 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 113 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 144
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 144 (accept_3_4 10 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 144 (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 144 (accept_3_4 7 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 144 (Polychromatic418967fa.accept_13_6_9_1_1_5604 6 113 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 144 (accept_3_4 4 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 113 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 144 (accept_3_4 1 113 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 144)))))))))))))))))))))))))))))))) (allB_succ' 33 112 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 112 144 16 2 7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 112 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 112 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 144 2 15 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 144 (accept_3_5 29 112 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 144 4 7 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 112 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 144 2 13 56 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 144
  (Polychromatic418967fa.accept_11_3_2_1_1_994 25 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 144 8 3 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 112 144 (accept_3_5 23 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  112 144 2 11 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 112 144 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 112 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 144 4 5 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 144 (Polychromatic418967fa.accept_13_6_8_1_1_2913
  19 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 144 2 9 56 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 144
  (accept_3_5 17 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 144 16 1 7 9 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 144
  (Polychromatic418967fa.accept_17_15_10_8_1_1708 15 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 144 2 7 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 144 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 112 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 144 4 3 28 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 144 (accept_3_5 11 112 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 144 2 5 56 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 144
  (Polychromatic418967fa.accept_13_9_8_1_1_824 9 112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 144 8 1 14 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 112 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 144 2 3 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 144 (accept_3_5 5 112 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 144 4 1 28 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 112 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 144 2 1 56 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 144 (Polychromatic418967fa.accept_15_1_7_9_1_20 1
  112 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  144))))))))))))))))))))))))))))))))) (allB_succ' 34 111 144 (Eq.refl Bool.true) (allA_succ_of_gcd 33 111 144 3 11 37
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 144
  (Polychromatic418967fa.accept_13_6_7_1_1_335 32 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 111 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 144 3 10 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 144 (Polychromatic418967fa.accept_13_3_7_1_1_334
  29 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 144
  (Polychromatic418967fa.accept_17_11_9_8_1_5038 28 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 111 144 3 9 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 111 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 111
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 144 3 8 37 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 144 (Polychromatic418967fa.accept_26_22_7_14_1_7710 22 111 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 144 3 7 37 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 144
  (Polychromatic418967fa.accept_21_20_6_18_1_7709 20 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 111 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 111 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 144 3 6 37 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 144 3 5 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 144 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  14 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 144
  (Polychromatic418967fa.accept_19_13_16_11_1_6047 13 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 111 144 3 4 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 111 144 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 111 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 144 3 3 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 144 (Polychromatic418967fa.accept_13_8_7_1_1_1385 8 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 111 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 144 3 2 37 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 144 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 111 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 144 3 1 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 111 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 144
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 111 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 144)))))))))))))))))))))))))))))))))) (allB_succ' 35 110 144 (Eq.refl Bool.true) (allA_succ_of_gcd 34
  110 144 2 17 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 110 144 (Polychromatic418967fa.accept_13_7_6_1_1_368 33 110 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 110 144 2 16 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 110 144 (accept_3_4 31 110 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 110 144 2 15 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 110 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 110 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 144 2 14 55 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 144 2 13 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 144 (accept_3_4 25 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 144 2 12 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 110 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 144 2 11 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 144
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 144 2 10 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 144 (accept_3_4 19 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 144 2 9 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 144 (Polychromatic418967fa.accept_27_17_2_9_1_5565 17 110 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 144 2 8 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15
  110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 144 2 7 55 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 144 (accept_3_4 13
  110 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 144 2 6 55 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 144
  (Polychromatic418967fa.accept_15_11_5_9_1_3205 11 110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 144 2 5 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 110 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 144 2 4 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 144 (accept_3_4 7 110 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 144 2 3 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 144 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 110 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 144 2 2 55 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 144 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3
  110 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 144 2 1 55 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 144 (accept_3_4 1
  110 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110 144))))))))))))))))))))))))))))))))))) (allB_succ' 36
  109 144 (Eq.refl Bool.true) (allA_succ_of_accept 35 109 144 (accept_3_5 35 109 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 109 144 (Polychromatic418967fa.accept_13_8_5_1_1_1381 34 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 109 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 33 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 109 144 (accept_3_5 32 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 109 144 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 109 144 (Polychromatic418967fa.accept_13_4_5_1_1_833 30 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 109 144 (accept_3_5 29 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 109 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 109
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 109 144
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 109 144 (accept_3_5 26 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 109 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 109 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 109 144 (accept_3_5 23 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 109 144 (Polychromatic418967fa.accept_13_9_5_1_1_1382 22 109
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 109 144
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 109 144 (accept_3_5 20 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 109 144 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 109 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 109 144 (accept_3_5 17 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 109 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 109
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 109 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 109 144 (accept_3_5 14 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 109 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 109 144 (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 109 144 (accept_3_5 11 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 109 144 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 109
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 109 144
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 109 144 (accept_3_5 8 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  109 144 (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 109 144 (Polychromatic418967fa.accept_13_6_5_1_1_834 6 109 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 109 144 (accept_3_5 5 109 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 109 144 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 109 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 109 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 3 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 109 144 (accept_3_5 2 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  109 144 (Polychromatic418967fa.accept_14_1_11_4_1_3430 1 109 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 109 144)))))))))))))))))))))))))))))))))))) (allB_succ' 37 108 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 108 144 36 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 144 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 108 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 144 2 17 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 144 3 11 36 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 144 4 8 27 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 144
  (Polychromatic418967fa.accept_13_5_4_1_1_364 31 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 144 6 5 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 108 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 144 4 7 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 144 9 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 144 2 13 54 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 144
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 144 12 2 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 144 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 108 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 144 2 11 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 144 3 7 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 144 4 5 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 144 (Polychromatic418967fa.accept_10_9_8_4_1_970
  19 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 144 18 1 6 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 144
  (Polychromatic418967fa.accept_19_17_13_11_1_2222 17 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 108 144 4 4 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 144 3 5 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 144 2 7 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 108 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 144 12 1 9 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 144
  (Polychromatic418967fa.accept_21_11_3_18_1_3068 11 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 144 2 5 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 144 9 1 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 144 4 2 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 108 144 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 108 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 144 6 1 18 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 144
  (Polychromatic418967fa.accept_13_5_4_1_1_364 5 108 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 144 4 1 27 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 144 3 1 36 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 144 2 1 54 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 108 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108 144))))))))))))))))))))))))))))))))))))) (allB_succ' 38 107 144 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 107 144 (accept_3_4 37 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 107 144 (Polychromatic418967fa.accept_21_15_2_18_1_1815 36 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 144
  (Polychromatic418967fa.accept_27_8_26_9_1_7708 35 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 144 (accept_3_4 34 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 107 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 144 (accept_3_4 31 107 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 144 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 107
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 144
  (Polychromatic418967fa.accept_17_12_5_8_1_7680 29 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 144 (accept_3_4 28 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 144 (accept_3_4 25 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 144 (Polychromatic418967fa.accept_13_11_3_1_1_1397 24 107 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 23 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 144 (accept_3_4 22 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 144 (accept_3_4 19 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 144 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 107 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 144
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 144 (accept_3_4 16 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 144 (Polychromatic418967fa.accept_23_14_15_6_1_7707 14 107 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 144 (accept_3_4 13 107 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 107 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 144 (accept_3_4 10 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 144 (Polychromatic418967fa.accept_22_9_19_12_1_7706 9 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 144 (Polychromatic418967fa.accept_15_8_2_9_1_3200 8 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 144 (accept_3_4 7 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 107 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 144 (accept_3_4 4 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 107 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 144 (accept_3_4 1 107 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 144)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 106 144 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 106 144 2 19 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 106 144 (Polychromatic418967fa.accept_15_7_1_9_1_1500 37 106 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 106 144 2 18 53 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 106 144 (accept_3_5 35 106 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 106 144 2 17 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 106 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 33 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 106 144 2 16 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 106 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 106 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 106 144 2 15 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 106 144 (accept_3_5 29 106 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 106 144 2 14 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 106 144
  (Polychromatic418967fa.accept_22_5_18_12_1_7664 27 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 106 144 2 13 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 106 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 106 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 106 144 2 12 53 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 106 144 (accept_3_5 23 106 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 106 144 2 11 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 106 144
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 106 144 2 10 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 106 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 106 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 106 144 2 9 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 106 144 (accept_3_5 17 106 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 106 144 2 8 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 106 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 106 144 2 7 53 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 106 144
  (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 106 144 2 6 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 106 144 (accept_3_5 11 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  106 144 2 5 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 106 144 (Polychromatic418967fa.accept_13_9_2_1_1_813 9 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 106 144 2 4 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 106 144 (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 106 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 144 2 3 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 144 (accept_3_5 5 106 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 106 144 2 2 53 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 106 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 106 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 144 2 1 53 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 144
  (Polychromatic418967fa.accept_17_1_4_8_1_5049 1 106 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 106 144))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 105 144 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 105 144 3 13 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 105 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 38 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 144 (Polychromatic418967fa.accept_19_18_10_11_1_6058 37
  105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 144 3 12 35 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 105 144
  (Polychromatic418967fa.accept_20_15_5_4_1_4566 35 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 144 (Polychromatic418967fa.accept_19_15_10_11_1_4735 34 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 144 3 11 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 144
  (Polychromatic418967fa.accept_25_7_5_19_1_7705 32 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 144 3 10 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 144 (Polychromatic418967fa.accept_10_9_5_4_1_966
  29 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 144
  (Polychromatic418967fa.accept_22_6_17_12_1_7704 28 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 105 144 3 9 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 105 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 105 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 144
  (Polychromatic418967fa.accept_14_11_7_4_1_3449 25 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 105 144 3 8 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 105 144 (Polychromatic418967fa.accept_25_23_5_19_1_7650 23 105 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 144 (Polychromatic418967fa.accept_17_5_3_8_1_1697
  22 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 144 3 7 35 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 144
  (Polychromatic418967fa.accept_19_1_10_11_1_4721 20 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 105 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 105 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 144 3 6 35 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 144
  (Polychromatic418967fa.accept_14_3_7_4_1_118 17 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 144 3 5 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 144
  (Polychromatic418967fa.accept_22_14_17_12_1_5950 14 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 105 144 (Polychromatic418967fa.accept_17_13_3_8_1_6310 13 105 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 144 3 4 35 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 144
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 144 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 144 3 3 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 144 (Polychromatic418967fa.accept_19_8_10_11_1_7614 8 105
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 144
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 105 144 3 2 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 144 (Polychromatic418967fa.accept_26_4_1_14_1_7703 4 105
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 144 3 1 35 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 144
  (Polychromatic418967fa.accept_19_2_10_11_1_7616 2 105 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 105 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105 144)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 104 144
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 104 144 8 5 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 104 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 104 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 104 144 2 19 52 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 104 144 (accept_3_4 37 104 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 104 144 4 9 26 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 104 144
  (Polychromatic418967fa.accept_15_5_14_9_1_274 35 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 104 144 2 17 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 104 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 144 8 4 13 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 144 (accept_3_4 31 104 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 144 2 15 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 144
  (Polychromatic418967fa.accept_22_7_16_12_1_7702 29 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 104 144 4 7 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 104 144 (Polychromatic418967fa.accept_15_12_14_9_1_778 27 104 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 144 2 13 52 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 144 (accept_3_4 25 104 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 144 8 3 13 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 104 144 2 11 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 104 144 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 104 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 104 144 4 5 26 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 104 144 (accept_3_4 19 104 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 104 144 2 9 52 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 104 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 104 144 8 2 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 104 144 (Polychromatic418967fa.accept_19_15_9_11_1_7514 15 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 144 2 7 52 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 144 (accept_3_4 13 104 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 144 4 3 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 144 (Polychromatic418967fa.accept_17_11_2_8_1_7569
  11 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 104 144 2 5 52 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 104 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 104 144 8 1 13 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 104 144 (accept_3_4 7 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 104
  144 2 3 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  104 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 104 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 104 144 4 1 26 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 104 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 144 2 1 52 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 144 (accept_3_4 1 104 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 144))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 103 144 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 103 144 (accept_3_5 41 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 103 144 (Polychromatic418967fa.accept_19_2_8_11_1_7701 40 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 103
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 144 (accept_3_5 38 103
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 103 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 144 (accept_3_5 35 103 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 103 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 144
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 33 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 144 (accept_3_5 32 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 144 (Polychromatic418967fa.accept_13_5_12_1_1_2123 31 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 144 (accept_3_5 29 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 144 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 144 (accept_3_5 26 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 144 (Polychromatic418967fa.accept_21_4_19_18_1_7542 25 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 144 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 144 (accept_3_5 23 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 103 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 144
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 144 (accept_3_5 20 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 144 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 144 (accept_3_5 17 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 103 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 144 (accept_3_5 14 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 144 (Polychromatic418967fa.accept_19_12_8_11_1_7554 12 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 144 (accept_3_5 11 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 144 (Polychromatic418967fa.accept_19_10_8_11_1_4708 10 103
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 144 (accept_3_5 8 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 144 (accept_3_5 5 103 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 144 (Polychromatic418967fa.accept_15_4_13_9_1_3197 4 103 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 144
  (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 144 (accept_3_5 2 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 103 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103 144)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 102 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 102 144 6 7 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 144 (Polychromatic418967fa.accept_27_14_21_9_1_3603 41 102 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 144 2 20 51 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 144 3 13 34 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 144 2 19 51 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 144
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 102 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 144 6 6 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 102 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 102 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 144 2 17 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 144 3 11 34 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 144 2 16 51 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 144
  (Polychromatic418967fa.accept_19_12_7_11_1_7658 31 102 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 102 144 6 5 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 102 144 (Polychromatic418967fa.accept_13_3_11_1_1_2122 29 102 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 144 2 14 51 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 144 3 9 34 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 144 2 13 51 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 144
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 102 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 102 144 6 4 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 102 144 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 102 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 144 2 11 51 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 144 3 7 34 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 144 2 10 51 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 144
  (Polychromatic418967fa.accept_15_4_12_9_1_773 19 102 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 144 6 3 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 102 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 144 2 8 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 144 3 5 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 144 2 7 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 144 (Polychromatic418967fa.accept_11_2_3_1_1_244
  13 102 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 144 6 2 17 24
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 144
  (Polychromatic418967fa.accept_22_11_14_12_1_7700 11 102 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 102 144 2 5 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 144 3 3 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 144 2 4 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 102 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 102 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 144 6 1 17 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 144
  (Polychromatic418967fa.accept_15_5_12_9_1_2253 5 102 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 102 144 2 2 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 102 144 3 1 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 102 144 2 1 51 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 144 (Polychromatic418967fa.accept_26_1_24_14_1_7699 1 102 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102 144))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 101 144
  (Eq.refl Bool.true) (allA_succ_of_accept 43 101 144 (accept_3_4 43 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 101 144 (Polychromatic418967fa.accept_23_19_9_6_1_7698 42 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 101 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 144 (accept_3_4 40 101 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 144
  (Polychromatic418967fa.accept_19_1_6_11_1_7548 39 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 101 144 (Polychromatic418967fa.accept_23_15_9_6_1_7697 38 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 144 (accept_3_4 37 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 101 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444
  35 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 144 (accept_3_4 34
  101 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 144
  (Polychromatic418967fa.accept_19_14_6_11_1_7599 33 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 144 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 101 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 144 (accept_3_4 31 101 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 144 (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 101
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 101 144 (accept_3_4 28 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 101 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 101 144 (Polychromatic418967fa.accept_17_9_16_8_1_2721 26 101 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 144 (accept_3_4 25 101 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 144 (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 101
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 144
  (Polychromatic418967fa.accept_20_3_1_4_1_7654 23 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 144 (accept_3_4 22 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 144 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 144 (accept_3_4 19 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 144 (Polychromatic418967fa.accept_19_18_6_11_1_7696 18 101 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 144
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 144 (accept_3_4 16 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 101 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 144 (accept_3_4 13 101 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 144 (Polychromatic418967fa.accept_25_12_1_19_1_7695 12 101
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 144
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 144 (accept_3_4 10 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 144 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 101 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 101 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 144 (accept_3_4 7 101 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 6
  101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 144
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 144 (accept_3_4 4 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 101 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 144 (Polychromatic418967fa.accept_15_2_11_9_1_263 2 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 144 (accept_3_4 1 101 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 144)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 100 144 (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 100 144 4 11 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 100 144 (Polychromatic418967fa.accept_27_16_19_9_1_7694 43 100 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 100 144 2 21 50 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 100 144 (accept_3_5 41
  100 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 100 144 4 10 25 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 100 144
  (Polychromatic418967fa.accept_23_16_8_6_1_5866 39 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 100 144 2 19 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 100 144 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 100 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 100 144 4 9 25 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 100 144 (accept_3_5 35 100 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 100 144 2 17 50 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 100 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 100 144 4 8 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 100 144 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 144 2 15 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 144 (accept_3_5 29 100 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 100 144 4 7 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 100 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 100 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 100 144 2 13 50 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 100 144
  (Polychromatic418967fa.accept_19_6_5_11_1_6067 25 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 100 144 4 6 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 100 144 (accept_3_5 23 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  100 144 2 11 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 100 144 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 144 4 5 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 19
  100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 100 144 2 9 50 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 100 144 (accept_3_5 17
  100 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 100 144 4 4 25 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 100 144
  (Polychromatic418967fa.accept_13_2_9_1_1_67 15 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 100 144 2 7 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 100 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 100 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 100 144 4 3 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 100 144 (accept_3_5 11 100 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 100 144 2 5 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 100 144 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 100 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 100 144 4 2 25 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 100 144
  (Polychromatic418967fa.accept_23_7_8_6_1_7693 7 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 100 144 2 3 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 100 144 (accept_3_5 5 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 100
  144 4 1 25 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  100 144 (Polychromatic418967fa.accept_15_3_10_9_1_769 3 100 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 100 144 2 1 50 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 100 144 (Polychromatic418967fa.accept_15_1_10_9_1_1495 1 100 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100 144))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  99 144 (Eq.refl Bool.true) (allA_succ_of_gcd 45 99 144 9 5 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 99 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 44 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 43 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 99 144 3 14 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 99 144 (Polychromatic418967fa.accept_17_7_14_8_1_5069 41 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 99 144 3 13 33 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 99 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 38 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 144 (Polychromatic418967fa.accept_13_11_8_1_1_3815 37 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 99 144 9 4 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 99 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 144
  (Polychromatic418967fa.accept_19_15_4_11_1_7652 34 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 99 144 3 11 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 99 144 (Polychromatic418967fa.accept_13_6_8_1_1_2913 32 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 99 144 3 10 33 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 99 144
  (Polychromatic418967fa.accept_20_9_19_4_1_3202 29 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 99 144 9 3 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 99 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 99 144 3 8 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 99 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 144 (Polychromatic418967fa.accept_13_9_8_1_1_824 22 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 99 144 3 7 33 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 99 144
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 20 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 99 144 9 2 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 99 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 144
  (Polychromatic418967fa.accept_17_16_14_8_1_7608 16 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 99 144 3 5 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 99 144 (Polychromatic418967fa.accept_20_14_19_4_1_7534 14 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 99 144 3 4 33 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 99 144
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 99 144 9 1 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 99 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 144
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 99 144 3 2 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 99 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 144 (Polychromatic418967fa.accept_22_4_11_12_1_7692 4 99 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 99 144 3 1 33 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 99 144
  (Polychromatic418967fa.accept_19_2_4_11_1_7507 2 99 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 144 (Polychromatic418967fa.accept_21_1_15_18_1_7646 1 99 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 99 144)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 98 144
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 98 144 2 23 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 98 144 (Polychromatic418967fa.accept_13_6_7_1_1_335 45 98 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 98 144 2 22 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 98 144 (accept_3_4 43 98 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 144 2 21 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 144
  (Polychromatic418967fa.accept_21_20_14_18_1_7524 41 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 98 144 2 20 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 98 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 98 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 144 2 19 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 144 (accept_3_4 37 98 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 144 2 18 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 144
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 98 144 2 17 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 98 144 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 98 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 144 2 16 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 144 (accept_3_4 31 98 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 144 2 15 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 98 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 144 2 14 49 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 144
  (Polychromatic418967fa.accept_19_8_3_11_1_6048 27 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 144 2 13 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 98 144 (accept_3_4 25 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98
  144 2 12 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  98 144 (Polychromatic418967fa.accept_19_4_3_11_1_7648 23 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 98 144 2 11 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 98 144 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 98 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 144 2 10 49 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 144 (accept_3_4 19 98 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 144 2 9 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 144 (Polychromatic418967fa.accept_15_2_8_9_1_4294
  17 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 144 2 8 49 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 144
  (Polychromatic418967fa.accept_17_15_13_8_1_7603 15 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 144 2 7 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 144 (accept_3_4 13 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  144 2 6 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 144 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 144 2 5 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 98 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 144 2 4 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 144 (accept_3_4 7 98 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 144 2 3 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 144 (Polychromatic418967fa.accept_17_5_13_8_1_7556 5 98 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 144 2 2 49 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 144
  (Polychromatic418967fa.accept_13_3_7_1_1_334 3 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 144 2 1 49 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 144 (accept_3_4 1 98 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  144))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 97 144 (Eq.refl Bool.true) (allA_succ_of_accept 47
  97 144 (accept_3_5 47 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 97 144
  (Polychromatic418967fa.accept_13_7_6_1_1_368 46 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 97 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 97 144 (accept_3_5 44 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 97 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 43 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 97 144 (Polychromatic418967fa.accept_10_2_7_4_1_967
  42 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 97 144 (accept_3_5 41
  97 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 97 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 97 144 (Polychromatic418967fa.accept_17_5_12_8_1_6304 39 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 97 144 (accept_3_5 38 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 97 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 97 144
  (Polychromatic418967fa.accept_21_15_13_18_1_7523 36 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 97 144 (accept_3_5 35 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 97 144 (Polychromatic418967fa.accept_13_8_6_1_1_3808 34 97 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 97 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 97 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 97 144 (accept_3_5 32 97 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 97 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 97 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 97 144 (accept_3_5 29 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  97 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 97 144 (Polychromatic418967fa.accept_17_10_12_8_1_2748 27 97 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 97 144 (accept_3_5 26 97 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 97 144 (Polychromatic418967fa.accept_21_4_13_18_1_137 25 97
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 97 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 97 144 (accept_3_5 23 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  97 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 97 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 97 144 (accept_3_5 20 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 97 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 97 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 97 144
  (Polychromatic418967fa.accept_13_5_6_1_1_822 18 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 97 144 (accept_3_5 17 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  97 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 97 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 97 144 (accept_3_5 14 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 97 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 97 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 97 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 97 144 (accept_3_5 11 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  97 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 97 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 97 144 (accept_3_5 8 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 97 144 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 97 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 97 144
  (Polychromatic418967fa.accept_21_6_13_18_1_1741 6 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 97 144 (accept_3_5 5 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 97
  144 (Polychromatic418967fa.accept_17_4_12_8_1_3833 4 97 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 97 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 97 144 (accept_3_5 2 97 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 97 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 97 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 97 144))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 96 144 (Eq.refl Bool.true) (allA_succ_of_gcd 48 96 144 48 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 144 (Polychromatic418967fa.accept_13_8_5_1_1_1381
  47 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 96 144 2 23 48 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 96 144 3 15 32 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 96 144 4 11 24 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 96 144 6 7 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 96 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 96 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 144 8 5 12 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 96 144 3 13 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 96 144 2 19 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 96 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 144 12 3 8 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 96 144
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 96 144 2 17 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 96 144 3 11 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 96 144 16 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 31 96 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 144 6 5 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 96 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 96 144 4 7 24 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 96 144 3 9 32 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 96 144 2 13 48 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 144
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 96 144 24 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 96 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 96 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 144 2 11 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 96 144 3 7 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 96 144 4 5 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 96 144 (Polychromatic418967fa.accept_13_6_5_1_1_834 19
  96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96 144 6 3 16 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 96 144
  (Polychromatic418967fa.accept_13_4_5_1_1_833 17 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 96 144 16 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 96 144 3 5 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 96 144 2 7 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 96 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 96 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 144 12 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 96 144 (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 96 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 144 2 5 48 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 96 144 3 3 32 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 96 144 8 1 12 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 96 144
  (Polychromatic418967fa.accept_21_7_12_18_1_3040 7 96 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 96 144 6 1 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 96 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 96 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 96 144 4 1 24 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 96 144 3 1 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 96 144 2 1 48 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 96 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 96
  144))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 95 144 (Eq.refl Bool.true) (allA_succ_of_accept 49
  95 144 (accept_3_4 49 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 95 144
  (Polychromatic418967fa.accept_15_3_5_9_1_764 48 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 95 144 (Polychromatic418967fa.accept_21_5_11_18_1_1789 47 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 144 (accept_3_4 46 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 95 144 (Polychromatic418967fa.accept_20_5_15_4_1_7635 45 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 144
  (Polychromatic418967fa.accept_13_5_4_1_1_364 44 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 95 144 (accept_3_4 43 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  95 144 (Polychromatic418967fa.accept_13_3_4_1_1_363 42 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 95 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 41 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 144 (accept_3_4 40 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 144
  (Polychromatic418967fa.accept_22_16_7_12_1_7630 38 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 144 (accept_3_4 37 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 144 (Polychromatic418967fa.accept_14_7_11_4_1_3455 35 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 144 (accept_3_4 34 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 144 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 95 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 144
  (Polychromatic418967fa.accept_17_15_10_8_1_1708 32 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 144 (accept_3_4 31 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 144 (Polychromatic418967fa.accept_20_10_15_4_1_7525 30 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 29 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 144 (accept_3_4 28 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 144 (Polychromatic418967fa.accept_15_12_5_9_1_3234 27 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 144
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 144 (accept_3_4 25 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 144 (Polychromatic418967fa.accept_21_3_11_18_1_805 24 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 144 (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 144 (accept_3_4 22 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 95 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 144
  (Polychromatic418967fa.accept_21_20_11_18_1_3037 20 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 95 144 (accept_3_4 19 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 95 144 (Polychromatic418967fa.accept_13_5_4_1_1_364 18 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 95 144 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 95 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 144 (accept_3_4 16 95 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 144 (Polychromatic418967fa.accept_14_1_11_4_1_3430
  15 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 144
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 144 (accept_3_4 13 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 144 (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 144 (accept_3_4 10 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 95 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 144
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 144 (accept_3_4 7 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  144 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 144 (Polychromatic418967fa.accept_13_5_4_1_1_364 5 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 144 (accept_3_4 4 95 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 144 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 95 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 144 (Polychromatic418967fa.accept_17_2_10_8_1_7691
  2 95 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 144 (accept_3_4 1 95
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 144))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 51 94 144 (Eq.refl Bool.true) (allA_succ_of_gcd 50 94 144 2 25 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 94 144
  (Polychromatic418967fa.accept_11_5_6_1_1_988 49 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 94 144 2 24 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 94 144 (accept_3_5 47 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 94
  144 2 23 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  94 144 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 94 144 2 22 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 94 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 94 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 94 144 2 21 47 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 94 144 (accept_3_5 41 94 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 94 144 2 20 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 94 144
  (Polychromatic418967fa.accept_19_1_18_11_1_4704 39 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 94 144 2 19 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 94 144 (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 94 144 2 18 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 94 144 (accept_3_5 35 94 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 94 144 2 17 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 94 144 (Polychromatic418967fa.accept_13_7_3_1_1_814 33 94 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 94 144 2 16 47 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 94 144
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 94 144 2 15 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 94 144 (accept_3_5 29 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 94
  144 2 14 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  94 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 94 144 2 13 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 94 144 (Polychromatic418967fa.accept_15_10_4_9_1_3203 25 94 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 94 144 2 12 47 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 94 144 (accept_3_5 23 94 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 94 144 2 11 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 94 144
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 94 144 2 10 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 94 144 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 94 144 2 9 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 94 144 (accept_3_5 17 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 94 144 2 8 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 94 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 94 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 94 144 2 7 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 94 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 94 144 2 6 47 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 94 144 (accept_3_5 11
  94 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 94 144 2 5 47 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 94 144
  (Polychromatic418967fa.accept_20_9_14_4_1_4540 9 94 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 94 144 2 4 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 94 144 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 94 144 2 3 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 94 144 (accept_3_5 5 94 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 94 144 2 2 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 94 144 (Polychromatic418967fa.accept_19_3_18_11_1_6074 3 94 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 94 144 2 1 47 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 94 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 94
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 94
  144))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 93 144 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  93 144 3 17 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 93 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 93 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 49 93 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 93 144 3 16 31 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 93 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 93 144 (Polychromatic418967fa.accept_19_8_17_11_1_3406 46 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 93 144 3 15 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 93 144 (Polychromatic418967fa.accept_14_2_9_4_1_1735
  44 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 144
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 93 144 3 14 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 93 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 93 144 3 13 31 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 93 144
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 38 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 93 144 3 12 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 93 144 (Polychromatic418967fa.accept_13_9_2_1_1_813 35
  93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 34 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 93 144 3 11 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 32 93 144 (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 144 (Polychromatic418967fa.accept_20_11_13_4_1_7573 31 93
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 93 144 3 10 31 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 93 144
  (Polychromatic418967fa.accept_10_9_3_4_1_985 29 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 93 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 93 144 3 9 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 93 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 144
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 93 144 3 8 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 93 144 (Polychromatic418967fa.accept_15_8_3_9_1_4220 23 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 144 (Polychromatic418967fa.accept_13_9_2_1_1_813 22 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 93 144 3 7 31 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 93 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 20 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 93 144 3 6 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 93 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 144
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 93 144 3 5 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 93 144 (Polychromatic418967fa.accept_19_14_17_11_1_7501 14 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 93 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 93 144 3 4 31 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 93 144
  (Polychromatic418967fa.accept_20_11_13_4_1_7573 11 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 93 144 (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 93 144 3 3 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 93 144 (Polychromatic418967fa.accept_15_8_3_9_1_4220 8 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 93 144
  (Polychromatic418967fa.accept_10_7_3_4_1_978 7 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 93 144 3 2 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 93 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 144 (Polychromatic418967fa.accept_19_4_17_11_1_7527 4 93 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 93 144 3 1 31 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 93 144
  (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 93 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 93 144 (Polychromatic418967fa.accept_21_1_9_18_1_4428 1 93 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 93 144)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 92
  144 (Eq.refl Bool.true) (allA_succ_of_gcd 52 92 144 4 13 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 92 144 (Polychromatic418967fa.accept_19_13_16_11_1_6047 51 92
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 144 2 25 46 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 144 (accept_3_4 49
  92 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 144 4 12 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 144 2 23 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 92 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 92 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 144 4 11 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 144 (accept_3_4 43 92 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 144 2 21 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 144 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 92 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 144 4 10 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 144
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 144 2 19 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 92 144 (accept_3_4 37 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92
  144 4 9 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  92 144 (Polychromatic418967fa.accept_17_1_7_8_1_6347 35 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 92 144 2 17 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 92 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 92 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 144 4 8 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 144 (accept_3_4 31 92 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 144 2 15 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 144 (Polychromatic418967fa.accept_27_2_11_9_1_7690
  29 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 144 4 7 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 144
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 144 2 13 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 92 144 (accept_3_4 25 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92
  144 4 6 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  92 144 (Polychromatic418967fa.accept_15_8_2_9_1_3200 23 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 92 144 2 11 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 92 144 (Polychromatic418967fa.accept_17_4_7_8_1_7491 21 92 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 144 4 5 23 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 144 (accept_3_4 19 92 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 144 2 9 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 92 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 144 4 4 23 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 144
  (Polychromatic418967fa.accept_19_15_16_11_1_7689 15 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 92 144 2 7 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 92 144 (accept_3_4 13 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 92 144 4 3 23 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 92 144 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 92 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 92 144 2 5 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 92 144 (Polychromatic418967fa.accept_21_9_8_18_1_7516 9 92 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 144 4 2 23 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 144 (accept_3_4 7 92 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 144 2 3 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 92 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 92
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 144 4 1 23 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 3 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 144 2 1 46 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 144 (accept_3_4 1 92 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  144))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 91 144 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 91 144 (accept_3_5 53 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  91 144 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 91 144 (Polychromatic418967fa.accept_15_6_1_9_1_1476 51 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 91 144 (accept_3_5 50 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 91 144 (Polychromatic418967fa.accept_17_15_6_8_1_6343 49 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 91 144
  (Polychromatic418967fa.accept_17_14_6_8_1_7688 48 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 91 144 (accept_3_5 47 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  91 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 46 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 91 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 91 144 (accept_3_5 44 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 91 144 (Polychromatic418967fa.accept_17_9_6_8_1_6315 43 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 91 144
  (Polychromatic418967fa.accept_19_4_15_11_1_7498 42 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 91 144 (accept_3_5 41 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  91 144 (Polychromatic418967fa.accept_15_10_1_9_1_5356 40 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 91 144 (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 91 144 (accept_3_5 38 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 91 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 37 91 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 91 144
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 36 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 91 144 (accept_3_5 35 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  91 144 (Polychromatic418967fa.accept_21_13_7_18_1_5966 34 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 91 144 (Polychromatic418967fa.accept_19_14_15_11_1_4739 33 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 91 144 (accept_3_5 32 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 91 144 (Polychromatic418967fa.accept_14_3_7_4_1_118 31 91 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 91 144
  (Polychromatic418967fa.accept_20_10_11_4_1_7562 30 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 91 144 (accept_3_5 29 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  91 144 (Polychromatic418967fa.accept_19_9_15_11_1_7687 28 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 91 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 91 144 (accept_3_5 26 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 91 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 91 144
  (Polychromatic418967fa.accept_11_2_3_1_1_244 24 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 91 144 (accept_3_5 23 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  91 144 (Polychromatic418967fa.accept_15_7_1_9_1_1500 22 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 91 144 (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 91 144 (accept_3_5 20 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 91 144 (Polychromatic418967fa.accept_21_19_7_18_1_7686 19 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 91 144
  (Polychromatic418967fa.accept_25_18_16_19_1_7685 18 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 91 144 (accept_3_5 17 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 91 144 (Polychromatic418967fa.accept_19_16_15_11_1_7684 16 91 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 91 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 91 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 91 144 (accept_3_5 14 91 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 91 144 (Polychromatic418967fa.accept_11_2_3_1_1_244
  13 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 91 144
  (Polychromatic418967fa.accept_21_12_7_18_1_7683 12 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 91 144 (accept_3_5 11 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  91 144 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 91 144 (Polychromatic418967fa.accept_17_9_6_8_1_6315 9 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 91 144 (accept_3_5 8 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 91 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 91 144
  (Polychromatic418967fa.accept_15_6_1_9_1_1476 6 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 91 144 (accept_3_5 5 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 91
  144 (Polychromatic418967fa.accept_19_4_15_11_1_7498 4 91 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 91 144 (Polychromatic418967fa.accept_14_3_7_4_1_118 3 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 91 144 (accept_3_5 2 91 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 91 144 (Polychromatic418967fa.accept_19_1_15_11_1_4712 1 91 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 91
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 90 144 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 90 144 18 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 90 144 (Polychromatic418967fa.accept_19_15_14_11_1_7682 53 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 90 144 2 26 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 90 144 3 17 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 90 144 2 25 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 144 (Polychromatic418967fa.accept_21_7_6_18_1_7681
  49 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 144 6 8 15 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 47 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 90 144 2 23 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 90 144 9 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 90 144 2 22 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 90 144 (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 144 6 7 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 144 (Polychromatic418967fa.accept_13_2_12_1_1_343 41 90 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 144 2 20 45 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 90 144 3 13 30 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 90 144 2 19 45 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 90 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 90 144 18 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 90 144 (Polychromatic418967fa.accept_19_16_14_11_1_4711 35 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 90 144 2 17 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 90 144 3 11 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 90 144 2 16 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 31
  90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 144 6 5 15 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 144
  (Polychromatic418967fa.accept_17_12_5_8_1_7680 29 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 144 2 14 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 90 144 9 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 90 144 2 13 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 90 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 144 6 4 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 90 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 144 2 11 45 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 90 144 3 7 30 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 90 144 2 10 45 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 90 144 18 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 90 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 144 2 8 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 90 144 3 5 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 90 144 2 7 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 144 (Polychromatic418967fa.accept_17_13_5_8_1_896 13 90 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 144 6 2 15 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 90 144
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 90 144 2 5 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 90 144 9 1 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 90 144 2 4 45 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 144 (Polychromatic418967fa.accept_19_7_14_11_1_4724 7 90 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 144 6 1 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 90 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 144 2 2 45 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 90 144 3 1 30 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 90 144 2 1 45 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 144
  (Polychromatic418967fa.accept_20_1_10_4_1_7518 1 90 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 90 144))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 89 144 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 89 144 (accept_3_4 55 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 144 (Polychromatic418967fa.accept_19_16_13_11_1_7679 54 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 53 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 144 (accept_3_4 52 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 144 (accept_3_4 49 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 48 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 144 (Polychromatic418967fa.accept_13_8_11_1_1_3789 47 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 144 (accept_3_4 46 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 89 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 44 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 144 (accept_3_4 43 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 144 (Polychromatic418967fa.accept_13_3_11_1_1_2122 42 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 144 (accept_3_4 40 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 144 (Polychromatic418967fa.accept_20_19_9_4_1_7560 39 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 144
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 144 (accept_3_4 37 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 144 (accept_3_4 34 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 144
  (Polychromatic418967fa.accept_21_11_5_18_1_5998 32 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 144 (accept_3_4 31 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 144 (accept_3_4 28 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 144
  (Polychromatic418967fa.accept_19_7_13_11_1_1208 26 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 144 (accept_3_4 25 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 144 (Polychromatic418967fa.accept_17_7_4_8_1_7678 24 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 144 (accept_3_4 22 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 144 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 20 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 144 (accept_3_4 19 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 144 (Polychromatic418967fa.accept_19_17_13_11_1_2222 17 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 144 (accept_3_4 16 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 89 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 144
  (Polychromatic418967fa.accept_20_14_9_4_1_7517 14 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 144 (accept_3_4 13 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 144 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 144 (Polychromatic418967fa.accept_21_11_5_18_1_5998 11 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 144 (accept_3_4 10 89 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 89 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 8 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 144 (accept_3_4 7 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  144 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 144 (accept_3_4 4 89 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 89 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 2
  89 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 144 (accept_3_4 1 89 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 57 88 144 (Eq.refl Bool.true) (allA_succ_of_gcd 56 88 144 8 7 11 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 88 144
  (Polychromatic418967fa.accept_21_13_4_18_1_7553 55 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 88 144 2 27 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 88 144 (accept_3_5 53 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 88
  144 4 13 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  88 144 (Polychromatic418967fa.accept_19_13_12_11_1_1249 51 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 88 144 2 25 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 88 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 49 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 88 144 8 6 11 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 88 144 (accept_3_5 47 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 88 144 2 23 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 88 144 (Polychromatic418967fa.accept_19_7_12_11_1_7621
  45 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 88 144 4 11 22 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 88 144
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 43 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 88 144 2 21 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 88 144 (accept_3_5 41 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 88
  144 8 5 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  88 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 88 144 2 19 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 88 144 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 88 144 4 9 22 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 88 144 (accept_3_5 35 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 88 144 2 17 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 88 144 (Polychromatic418967fa.accept_15_3_13_9_1_3196
  33 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 88 144 8 4 11 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 88 144
  (Polychromatic418967fa.accept_25_6_13_19_1_7677 31 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 88 144 2 15 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 88 144 (accept_3_5 29 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 88
  144 4 7 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  88 144 (Polychromatic418967fa.accept_19_8_12_11_1_7676 27 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 88 144 2 13 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 88 144 (Polychromatic418967fa.accept_23_2_19_6_1_7675 25 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 88 144 8 3 11 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 88 144 (accept_3_5 23 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 88 144 2 11 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 88 144
  (Polychromatic418967fa.accept_25_21_13_19_1_7674 21 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 88 144 4 5 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 88 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 19 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 88 144 2 9 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 88 144 (accept_3_5 17 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 88 144 8 2 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 88 144 (Polychromatic418967fa.accept_25_15_13_19_1_7673 15 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 88 144 2 7 44 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 88 144
  (Polychromatic418967fa.accept_17_13_3_8_1_6310 13 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 88 144 4 3 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 88 144 (accept_3_5 11 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 88
  144 2 5 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  88 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 88 144 8 1 11 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 88 144 (Polychromatic418967fa.accept_15_7_13_9_1_1466 7 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 88 144 2 3 44 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 88 144 (accept_3_5 5 88 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 88 144 4 1 22 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 88 144 (Polychromatic418967fa.accept_15_3_13_9_1_3196 3 88 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 88 144 2 1 44 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 88 144
  (Polychromatic418967fa.accept_19_1_12_11_1_1245 1 88 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 88 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 87 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 87 144 3 19 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 87 144 (Polychromatic418967fa.accept_25_6_12_19_1_7672 56 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 87 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 87 144 3 18 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 87 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 53 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 87 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 87 144 3 17 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 87 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 50
  87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 87 144
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 49 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 87 144 3 16 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 87 144 (Polychromatic418967fa.accept_13_8_9_1_1_2147 47 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017 46 87
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 87 144 3 15 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 87 144
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 44 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 87 144 3 14 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 87 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 144
  (Polychromatic418967fa.accept_15_10_12_9_1_776 40 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 87 144 3 13 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 87 144 (Polychromatic418967fa.accept_21_17_3_18_1_7549 38 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 87 144 (Polychromatic418967fa.accept_13_11_9_1_1_1407 37 87
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 87 144 3 12 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 87 144
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 87 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 87 144 3 11 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 87 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 32
  87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 87 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 31 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 87 144 3 10 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 87 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 144 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 87 144 3 9 29 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 87 144
  (Polychromatic418967fa.accept_21_5_3_18_1_7508 26 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 144 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 87 144 3 8 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 87 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 87 144 3 7 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 87 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 87 144 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 87 144 3 6 29 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 87 144
  (Polychromatic418967fa.accept_20_17_7_4_1_7671 17 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 87 144 (Polychromatic418967fa.accept_17_16_2_8_1_7625 16 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 87 144 3 5 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 87 144 (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 87
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 87 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 87 144 3 4 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 87 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 144 (Polychromatic418967fa.accept_13_10_9_1_1_5609 10 87
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 87 144 3 3 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 87 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 144 (Polychromatic418967fa.accept_14_7_3_4_1_1816 7 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 87 144 3 2 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 87 144 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 144
  (Polychromatic418967fa.accept_15_4_12_9_1_773 4 87 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 87 144 3 1 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 87 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 87 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 87 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 86 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 86 144 2 29 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 86 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 57 86 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 144 2 28 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 144 (accept_3_4 55 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 144 2 27 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 144 (Polychromatic418967fa.accept_19_15_10_11_1_4735 53 86
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 144 2 26 43 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 144
  (Polychromatic418967fa.accept_13_12_8_1_1_825 51 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 144 2 25 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 86 144 (accept_3_4 49 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86
  144 2 24 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 47 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 144 2 23 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 86 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 144 2 22 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 144 (accept_3_4 43 86 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 144 2 21 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 144 2 20 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 144 (Polychromatic418967fa.accept_19_1_10_11_1_4721 39 86 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 144 2 19 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 144 (accept_3_4 37 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 144 2 18 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 86 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 144 2 17 43 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 144 2 16 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 144 (accept_3_4 31 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  144 2 15 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 144 (Polychromatic418967fa.accept_25_4_11_19_1_7670 29 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 144 2 14 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 86 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 144 2 13 43 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 144 (accept_3_4 25 86 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 144 2 12 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 144
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 144 2 11 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 144 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 86 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 144 2 10 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 144 (accept_3_4 19 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 144 2 9 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 144 (Polychromatic418967fa.accept_15_2_11_9_1_263 17 86 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 144 2 8 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 144
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 144 2 7 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 144 (accept_3_4 13 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  144 2 6 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 144 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 144 2 5 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 144 (Polychromatic418967fa.accept_13_9_8_1_1_824 9 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 144 2 4 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 144 (accept_3_4 7 86 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 144 2 3 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 86 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 144 2 2 43 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 144
  (Polychromatic418967fa.accept_19_3_10_11_1_7669 3 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 144 2 1 43 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 144 (accept_3_4 1 86 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 85 144 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 85 144 (accept_3_5 59 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  85 144 (Polychromatic418967fa.accept_13_6_7_1_1_335 58 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 85 144 (Polychromatic418967fa.accept_15_12_10_9_1_798 57 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 85 144 (accept_3_5 56 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 85 144 (Polychromatic418967fa.accept_13_3_7_1_1_334 55 85 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 85 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 54 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 85 144 (accept_3_5 53 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  85 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 85 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 85 144 (accept_3_5 50 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 85 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 49 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 85 144
  (Polychromatic418967fa.accept_11_4_8_1_1_1047 48 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 85 144 (accept_3_5 47 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  85 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 85 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 85 144 (accept_3_5 44 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 85 144 (Polychromatic418967fa.accept_26_17_7_14_1_7668 43 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 85 144
  (Polychromatic418967fa.accept_13_3_7_1_1_334 42 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 85 144 (accept_3_5 41 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  85 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 85 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 85 144 (accept_3_5 38 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 85 144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 37 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 85 144
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 85 144 (accept_3_5 35 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  85 144 (Polychromatic418967fa.accept_13_8_7_1_1_1385 34 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 85 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 85 144 (accept_3_5 32 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 85 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 85 144
  (Polychromatic418967fa.accept_20_10_5_4_1_7511 30 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 85 144 (accept_3_5 29 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  85 144 (Polychromatic418967fa.accept_22_6_19_12_1_7667 28 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 85 144 (Polychromatic418967fa.accept_15_12_10_9_1_798 27 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 85 144 (accept_3_5 26 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 85 144 (Polychromatic418967fa.accept_14_11_1_4_1_4445 25 85
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 85 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 85 144 (accept_3_5 23 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  85 144 (Polychromatic418967fa.accept_19_3_9_11_1_7666 22 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 85 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 85 144 (accept_3_5 20 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 85 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 85 144
  (Polychromatic418967fa.accept_15_3_10_9_1_769 18 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 85 144 (accept_3_5 17 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  85 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 85 144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 85 144 (accept_3_5 14 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 85 144 (Polychromatic418967fa.accept_23_13_16_6_1_7665 13 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 85 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 85 144 (accept_3_5 11 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  85 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 85 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 85 144 (accept_3_5 8 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 85 144 (Polychromatic418967fa.accept_19_7_9_11_1_7493 7 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 85 144
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 85 144 (accept_3_5 5 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 85
  144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 85 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 85 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 85 144 (accept_3_5 2 85 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 85 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 85 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 85
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 84 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 84 144 12 5 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 84 144 (Polychromatic418967fa.accept_13_7_6_1_1_368 59 84 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 144 2 29 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 84 144 3 19 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 84 144 4 14 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 144 (Polychromatic418967fa.accept_13_3_6_1_1_3797
  55 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 144 6 9 14 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 144
  (Polychromatic418967fa.accept_17_2_16_8_1_3881 53 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 84 144 4 13 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 84 144 3 17 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 84 144 2 25 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 84 144 (Polychromatic418967fa.accept_22_5_18_12_1_7664 49 84 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 144 12 4 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 144 (Polychromatic418967fa.accept_13_8_6_1_1_3808 47 84 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 144 2 23 42 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 84 144 3 15 28 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 84 144 4 11 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 144
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 43 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 84 144 6 7 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 84 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 84 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 144 4 10 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 84 144 3 13 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 84 144 2 19 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 144 (Polychromatic418967fa.accept_19_18_8_11_1_7663
  37 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 144 12 3 7 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 144
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 84 144 2 17 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 84 144 3 11 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 84 144 4 8 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 84 144 (Polychromatic418967fa.accept_13_5_6_1_1_822 31 84 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 144 6 5 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 144 (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 84 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 144 4 7 21 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 84 144 3 9 28 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 84 144 2 13 42 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 144
  (Polychromatic418967fa.accept_27_25_3_9_1_7662 25 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 84 144 12 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 84 144 (Polychromatic418967fa.accept_25_23_9_19_1_7661 23 84 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 144 2 11 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 84 144 3 7 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 84 144 4 5 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 144 (Polychromatic418967fa.accept_17_2_16_8_1_3881
  19 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 144 6 3 14 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 144
  (Polychromatic418967fa.accept_11_6_7_1_1_564 17 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 84 144 4 4 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 84 144 3 5 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 84 144 2 7 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 144 (Polychromatic418967fa.accept_31_13_22_20_1_7660 13 84 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 144 12 1 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 84 144 (Polychromatic418967fa.accept_22_11_18_12_1_7659 11 84
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 144 2 5 42 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 84 144 3 3 28 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 84 144 4 2 21 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 144
  (Polychromatic418967fa.accept_13_7_6_1_1_368 7 84 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 84 144 6 1 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 84 144 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 84 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 144 4 1 21 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 84 144 3 1 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 84 144 2 1 42 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 144 (Polychromatic418967fa.accept_19_1_8_11_1_3378 1 84 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 83 144 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 83 144 (accept_3_4 61 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  83 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 60 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 83 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 59 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 144 (accept_3_4 58 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 83 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 144
  (Polychromatic418967fa.accept_13_4_5_1_1_833 56 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 83 144 (accept_3_4 55 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  83 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 54 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 83 144 (Polychromatic418967fa.accept_19_15_7_11_1_7657 53 83 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 144 (accept_3_4 52 83 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 83 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 144
  (Polychromatic418967fa.accept_19_12_7_11_1_7658 50 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 83 144 (accept_3_4 49 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 144 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 144 (accept_3_4 46 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 83 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 144 (accept_3_4 43 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 42 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 144 (Polychromatic418967fa.accept_20_1_3_4_1_3213 41 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 144 (accept_3_4 40 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 83 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 38 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 144 (accept_3_4 37 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 144 (Polychromatic418967fa.accept_21_15_20_18_1_5985 36 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 144 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 144 (accept_3_4 34 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 83 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 144
  (Polychromatic418967fa.accept_13_6_5_1_1_834 32 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 144 (accept_3_4 31 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 29 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 144 (accept_3_4 28 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 83 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 26 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 144 (accept_3_4 25 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 144 (accept_3_4 22 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 144 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 83 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 144
  (Polychromatic418967fa.accept_22_20_17_12_1_7595 20 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 83 144 (accept_3_4 19 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 83 144 (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 83 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 144 (accept_3_4 16 83 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 144
  (Polychromatic418967fa.accept_19_15_7_11_1_7657 15 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 83 144 (Polychromatic418967fa.accept_15_14_8_9_1_1452 14 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 144 (accept_3_4 13 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 83 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 83 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 144
  (Polychromatic418967fa.accept_21_11_20_18_1_7656 11 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 83 144 (accept_3_4 10 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 83 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 144 (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 83 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 144 (accept_3_4 7 83 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83 144 (Polychromatic418967fa.accept_13_6_5_1_1_834 6
  83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 83 144 (accept_3_4 4 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83
  144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 83 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 83 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 83 144 (accept_3_4 1 83 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 83 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 82 144
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 82 144 2 31 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 82 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 61 82 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 82 144 2 30 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 82 144 (accept_3_5 59 82 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 82 144 2 29 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 82 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 57 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 82 144 2 28 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 82 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 82 144 2 27 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 82 144 (accept_3_5 53 82 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 82 144 2 26 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 82 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 82 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 82 144 2 25 41 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 82 144
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 82 144 2 24 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 82 144 (accept_3_5 47 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 82
  144 2 23 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  82 144 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 82 144 2 22 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 82 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 82 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 82 144 2 21 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 82 144 (accept_3_5 41 82 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 82 144 2 20 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 82 144
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 82 144 2 19 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 82 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 82 144 2 18 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 82 144 (accept_3_5 35 82 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 82 144 2 17 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 82 144 (Polychromatic418967fa.accept_17_16_14_8_1_7608 33 82
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 82 144 2 16 41 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 82 144
  (Polychromatic418967fa.accept_13_5_4_1_1_364 31 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 82 144 2 15 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 82 144 (accept_3_5 29 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 82
  144 2 14 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  82 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 82 144 2 13 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 82 144 (Polychromatic418967fa.accept_20_5_2_4_1_7655 25 82 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 82 144 2 12 41 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 82 144 (accept_3_5 23 82 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 82 144 2 11 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 82 144
  (Polychromatic418967fa.accept_23_21_13_6_1_7585 21 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 82 144 2 10 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 82 144 (Polychromatic418967fa.accept_20_19_2_4_1_2057 19 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 82 144 2 9 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 82 144 (accept_3_5 17 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 82 144 2 8 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 82 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 82 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 82 144 2 7 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 82 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13
  82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 82 144 2 6 41 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 82 144 (accept_3_5 11
  82 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 82 144 2 5 41 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 82 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 82 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 82 144 2 4 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 82 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 82 144 2 3 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 82 144 (accept_3_5 5 82 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 82 144 2 2 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 82 144 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 82 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 82 144 2 1 41 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 82 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 82
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 82
  144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 81 144 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 81 144 9 7 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 81 144 (Polychromatic418967fa.accept_22_18_15_12_1_7530 62 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 61 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 81 144 3 20 27 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 81 144
  (Polychromatic418967fa.accept_13_7_3_1_1_814 59 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 81 144 (Polychromatic418967fa.accept_13_6_3_1_1_1413 58 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 81 144 3 19 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 81 144 (Polychromatic418967fa.accept_13_4_3_1_1_2898
  56 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 81 144
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 55 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 81 144 9 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 81 144 (Polychromatic418967fa.accept_19_15_5_11_1_4719 53 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 144 (Polychromatic418967fa.accept_11_8_4_1_1_1000 52 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 81 144 3 17 27 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 81 144
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 144 (Polychromatic418967fa.accept_14_7_11_4_1_3455 49 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 81 144 3 16 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 81 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447
  47 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 144
  (Polychromatic418967fa.accept_13_7_3_1_1_814 46 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 81 144 9 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 81 144 (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 81 144 (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 81 144 3 14 27 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 81 144
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 81 144 (Polychromatic418967fa.accept_22_18_15_12_1_7530 40 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 81 144 3 13 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 81 144 (Polychromatic418967fa.accept_17_4_13_8_1_3874
  38 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 81 144
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 37 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 81 144 9 4 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 81 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 144 (Polychromatic418967fa.accept_15_4_6_9_1_2269 34 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 81 144 3 11 27 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 81 144
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 144 (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 81 144 3 10 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 81 144 (Polychromatic418967fa.accept_14_1_11_4_1_3430
  29 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 144
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 81 144 9 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 81 144 (Polychromatic418967fa.accept_15_11_6_9_1_3236 26 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 81 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 81 144 3 8 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 81 144
  (Polychromatic418967fa.accept_20_3_1_4_1_7654 23 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 81 144 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 81 144 3 7 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 81 144 (Polychromatic418967fa.accept_13_7_3_1_1_814 20 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 81 144
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 81 144 9 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 81 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 81 144 3 5 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 81 144
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 144 (Polychromatic418967fa.accept_19_13_5_11_1_7653 13 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 81 144 3 4 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 81 144 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 144
  (Polychromatic418967fa.accept_19_10_5_11_1_7597 10 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 81 144 9 1 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 81 144 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 81 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 81 144 3 2 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 81 144
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 81 144 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 81 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 81 144 3 1 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 81 144 (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 81 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 144
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 1 81 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 81 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 80 144 (Eq.refl
  Bool.true) (allA_succ_of_gcd 64 80 144 16 4 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 80 144 (Polychromatic418967fa.accept_14_7_10_4_1_130 63 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 144 2 31 40 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 144 (accept_3_4 61 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 144 4 15 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 144 (Polychromatic418967fa.accept_15_14_5_9_1_2284
  59 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 80 144 2 29 40 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 80 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 80 144 8 7 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 80 144 (accept_3_4 55 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80
  144 2 27 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  80 144 (Polychromatic418967fa.accept_19_15_4_11_1_7652 53 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 80 144 4 13 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 80 144 (Polychromatic418967fa.accept_13_12_2_1_1_2909 51 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 144 2 25 40 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 144 (accept_3_4 49 80 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 144 16 3 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 144 (Polychromatic418967fa.accept_22_3_14_12_1_7651
  47 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 144 2 23 40 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 144
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 144 4 11 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 144 (accept_3_4 43 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  144 2 21 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 41 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 144 8 5 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 80 144 (Polychromatic418967fa.accept_17_5_12_8_1_6304 39 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 144 2 19 40 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 144 (accept_3_4 37 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 144 4 9 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 80 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 144 2 17 40 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 144
  (Polychromatic418967fa.accept_15_3_5_9_1_764 33 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 144 16 2 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 144 (accept_3_4 31 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  144 2 15 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 144 4 7 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 144 2 13 40 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 144 (accept_3_4 25 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 144 8 3 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 144 (Polychromatic418967fa.accept_25_23_5_19_1_7650 23 80
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 144 2 11 40 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 144
  (Polychromatic418967fa.accept_14_7_10_4_1_130 21 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 144 4 5 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 144 (accept_3_4 19 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  144 2 9 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 144 (Polychromatic418967fa.accept_19_17_4_11_1_4731 17 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 144 16 1 5 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 144 2 7 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 144 (accept_3_4 13 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 144 4 3 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 144 (Polychromatic418967fa.accept_15_11_5_9_1_3205 11 80 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 144 2 5 40 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 144
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 144 8 1 10 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 144 (accept_3_4 7 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 144
  2 3 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  144 (Polychromatic418967fa.accept_17_5_12_8_1_6304 5 80 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 80 144 4 1 20 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 80 144 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 144 2 1 40 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 144 (accept_3_4 1 80 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 80 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66
  79 144 (Eq.refl Bool.true) (allA_succ_of_accept 65 79 144 (accept_3_5 65 79 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 64 79 144 (Polychromatic418967fa.accept_25_14_4_19_1_7649 64 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 79 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 63 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 79 144 (accept_3_5 62 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  79 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 79 144 (Polychromatic418967fa.accept_17_9_11_8_1_5077 60 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 79 144 (accept_3_5 59 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 79 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 58 79 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 79 144
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 57 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 79 144 (accept_3_5 56 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  79 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 55 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 79 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 79 144 (accept_3_5 53 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 79 144 (Polychromatic418967fa.accept_17_1_11_8_1_2725 52 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 79 144
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 51 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 79 144 (accept_3_5 50 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  79 144 (Polychromatic418967fa.accept_20_9_19_4_1_3202 49 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 79 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 79 144 (accept_3_5 47 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 79 144 (Polychromatic418967fa.accept_19_8_3_11_1_6048 46 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 79 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 79 144 (accept_3_5 44 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  79 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 43 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 79 144 (Polychromatic418967fa.accept_15_12_4_9_1_3204 42 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 79 144 (accept_3_5 41 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 79 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 79 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 79 144
  (Polychromatic418967fa.accept_19_1_3_11_1_7545 39 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 79 144 (accept_3_5 38 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  79 144 (Polychromatic418967fa.accept_19_18_3_11_1_6066 37 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 79 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 79 144 (accept_3_5 35 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 79 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 79 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 79 144 (accept_3_5 32 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  79 144 (Polychromatic418967fa.accept_17_14_11_8_1_3854 31 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 79 144 (Polychromatic418967fa.accept_14_2_9_4_1_1735 30 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 79 144 (accept_3_5 29 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 79 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 79 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 27 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 79 144 (accept_3_5 26 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  79 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 79 144 (Polychromatic418967fa.accept_21_3_16_18_1_7500 24 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 79 144 (accept_3_5 23 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 79 144 (Polychromatic418967fa.accept_20_2_19_4_1_3246 22 79
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 79 144
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 79 144 (accept_3_5 20 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  79 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 79 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 79 144 (accept_3_5 17 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 79 144 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 79 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 79 144 (accept_3_5 14 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  79 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 79 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 79 144 (accept_3_5 11 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 79 144 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 79 144
  (Polychromatic418967fa.accept_17_9_11_8_1_5077 9 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 79 144 (accept_3_5 8 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 79
  144 (Polychromatic418967fa.accept_27_7_25_9_1_3618 7 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 79 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 79 144 (accept_3_5 5 79 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 79 144 (Polychromatic418967fa.accept_19_4_3_11_1_7648 4 79 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 79 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 3 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 79 144 (accept_3_5 2 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 79
  144 (Polychromatic418967fa.accept_17_1_11_8_1_2725 1 79 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 79 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 78 144
  (Eq.refl Bool.true) (allA_succ_of_gcd 66 78 144 6 11 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 78 144 (Polychromatic418967fa.accept_15_5_3_9_1_283 65 78 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 144 2 32 39 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 78 144 3 21 26 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 78 144 2 31 39 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 61 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 78 144 6 10 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 78 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 59 78 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 78 144 2 29 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 78 144 3 19 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 78 144 2 28 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 144 (Polychromatic418967fa.accept_15_10_3_9_1_3285
  55 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 144 6 9 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 144
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 53 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 144 2 26 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 78 144 3 17 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 78 144 2 25 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 49 78 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 144 6 8 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 78 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 144 2 23 39 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 78 144 3 15 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 78 144 2 22 39 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 144
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 78 144 6 7 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 78 144 (Polychromatic418967fa.accept_19_3_2_11_1_7647 41 78 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 78 144 2 20 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 78 144 3 13 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 78 144 2 19 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 144
  (Polychromatic418967fa.accept_21_16_15_18_1_3050 37 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 78 144 6 6 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 78 144 (Polychromatic418967fa.accept_15_5_3_9_1_283 35 78 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 144 2 17 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 78 144 3 11 26 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 78 144 2 16 39 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 78 144 6 5 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 78 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 78 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 144 2 14 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 78 144 3 9 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 78 144 2 13 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 144 (Polychromatic418967fa.accept_14_11_8_4_1_2628
  25 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 144 6 4 13 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 144
  (Polychromatic418967fa.accept_15_8_3_9_1_4220 23 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 144 2 11 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 78 144 3 7 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 78 144 2 10 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 78 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 78 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 144 6 3 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 78 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 144 2 8 39 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 78 144 3 5 26 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 78 144 2 7 39 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 78 144
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 78 144 6 2 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 78 144 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 78 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 78 144 2 5 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 78 144 3 3 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 78 144 2 4 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 144 (Polychromatic418967fa.accept_21_7_15_18_1_7526 7 78 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 144 6 1 13 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 78 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 78 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 78 144 2 2 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 78 144 3 1 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 78 144 2 1 39 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 144 (Polychromatic418967fa.accept_21_1_15_18_1_7646 1 78 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 78 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 68 77 144 (Eq.refl Bool.true) (allA_succ_of_accept 67 77 144 (accept_3_4 67 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 144 (Polychromatic418967fa.accept_14_10_7_4_1_3453 66 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 144
  (Polychromatic418967fa.accept_19_8_1_11_1_4718 65 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 144 (accept_3_4 64 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 62 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 144 (accept_3_4 61 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 144 (Polychromatic418967fa.accept_13_8_12_1_1_4662 60 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 144
  (Polychromatic418967fa.accept_14_3_7_4_1_118 59 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 144 (accept_3_4 58 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 144 (Polychromatic418967fa.accept_13_5_12_1_1_2123 57 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 144 (Polychromatic418967fa.accept_15_11_2_9_1_1480 56 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 144 (accept_3_4 55 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 144 (Polychromatic418967fa.accept_13_2_12_1_1_343 54 77 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 53 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 144 (accept_3_4 52 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 51 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 144 (Polychromatic418967fa.accept_13_11_12_1_1_2154 50 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 144 (accept_3_4 49 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 144 (Polychromatic418967fa.accept_19_10_1_11_1_7532 48 77
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 144
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 47 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 144 (accept_3_4 46 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 144 (Polychromatic418967fa.accept_14_3_7_4_1_118 45 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 144 (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 144 (accept_3_4 43 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 77 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 41 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 144 (accept_3_4 40 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 144 (Polychromatic418967fa.accept_14_11_7_4_1_3449 39 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 144 (Polychromatic418967fa.accept_14_10_7_4_1_3453 38 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 144 (accept_3_4 37 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 144 (Polychromatic418967fa.accept_21_15_14_18_1_7645 36 77
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 144
  (Polychromatic418967fa.accept_17_1_9_8_1_7492 35 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 144 (accept_3_4 34 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 144 (accept_3_4 31 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 144 (Polychromatic418967fa.accept_21_9_14_18_1_7576 30 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 144
  (Polychromatic418967fa.accept_19_10_1_11_1_7532 29 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 144 (accept_3_4 28 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 144 (Polychromatic418967fa.accept_19_8_1_11_1_4718 27 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 144 (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 144 (accept_3_4 25 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 144 (Polychromatic418967fa.accept_13_11_12_1_1_2154 24 77
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 23 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 144 (accept_3_4 22 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 144 (Polychromatic418967fa.accept_21_20_14_18_1_7524 20 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 144 (accept_3_4 19 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 144 (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 77
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 144
  (Polychromatic418967fa.accept_14_3_7_4_1_118 17 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 144 (accept_3_4 16 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 144 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 144 (Polychromatic418967fa.accept_22_14_11_12_1_7644 14 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 144 (accept_3_4 13 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 77 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 144 (accept_3_4 10 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 144 (Polychromatic418967fa.accept_19_9_1_11_1_7643 9 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 144 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 144 (accept_3_4 7 77 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 144 (Polychromatic418967fa.accept_17_6_9_8_1_6316 6 77 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 144
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 144 (accept_3_4 4 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  144 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 77 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 77 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 144 (accept_3_4 1 77 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 76 144
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 76 144 4 17 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 76 144 (Polychromatic418967fa.accept_15_7_1_9_1_1500 67 76 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 76 144 2 33 38 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 76 144 (accept_3_5 65 76 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 76 144 4 16 19 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 76 144
  (Polychromatic418967fa.accept_23_17_7_6_1_7642 63 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 76 144 2 31 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 76 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 76 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 76 144 4 15 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 76 144 (accept_3_5 59 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 76 144 2 29 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 76 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 76 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 76 144 4 14 19 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 76 144
  (Polychromatic418967fa.accept_10_5_6_4_1_64 55 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 76 144 2 27 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 76 144 (accept_3_5 53 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 76
  144 4 13 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  76 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 76 144 2 25 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 76 144 (Polychromatic418967fa.accept_13_10_11_1_1_2152 49 76 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 76 144 4 12 19 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 76 144 (accept_3_5 47 76 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 76 144 2 23 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 76 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 45 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 76 144 4 11 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 76 144 (Polychromatic418967fa.accept_25_18_1_19_1_7641 43 76 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 76 144 2 21 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 76 144 (accept_3_5 41 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 76 144 4 10 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 76 144 (Polychromatic418967fa.accept_27_12_22_9_1_7640 39 76
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 76 144 2 19 38 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 76 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 37 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 76 144 4 9 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 76 144 (accept_3_5 35 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 76
  144 2 17 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  76 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 76 144 4 8 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 76 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 76 144 2 15 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 76 144 (accept_3_5 29 76 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 76 144 4 7 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 76 144 (Polychromatic418967fa.accept_21_6_13_18_1_1741 27 76
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 76 144 2 13 38 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 76 144
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 76 144 4 6 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 76 144 (accept_3_5 23 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 76
  144 2 11 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  76 144 (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 76 144 4 5 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 76 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 76 144 2 9 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 76 144 (accept_3_5 17 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 76 144 4 4 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 76 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 76 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 76 144 2 7 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 76 144
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 76 144 4 3 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 76 144 (accept_3_5 11 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 76
  144 2 5 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  76 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 76 144 4 2 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 76 144 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 76 144 2 3 38 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 76 144 (accept_3_5 5 76 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 76 144 4 1 19 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 76 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 76 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 76 144 2 1 38 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 76 144
  (Polychromatic418967fa.accept_23_1_7_6_1_7639 1 76 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 76 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 75 144 (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 75 144 3 23 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 75 144 (Polychromatic418967fa.accept_21_5_12_18_1_7637 68 75 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 75 144
  (Polychromatic418967fa.accept_17_16_7_8_1_7638 67 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 75 144 3 22 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 75 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 64 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 75 144 3 21 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 75 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 62 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 61 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 75 144 3 20 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 75 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 59
  75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 58 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 75 144 3 19 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 75 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 75 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 75 144 3 18 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 75 144
  (Polychromatic418967fa.accept_21_11_12_18_1_4455 53 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 75 144 (Polychromatic418967fa.accept_17_1_7_8_1_6347 52 75 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 75 144 3 17 25 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 75 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 50 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 49 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 75 144 3 16 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 75 144 (Polychromatic418967fa.accept_21_5_12_18_1_7637
  47 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 144
  (Polychromatic418967fa.accept_10_6_5_4_1_571 46 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 75 144 3 15 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 75 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 75 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 75 144 3 14 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 75 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 75 144 (Polychromatic418967fa.accept_21_19_12_18_1_1798 40 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 75 144 3 13 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 75 144 (Polychromatic418967fa.accept_17_4_7_8_1_7491
  38 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 75 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 37 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 75 144 3 12 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 75 144 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 75 144 3 11 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 75 144
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 31 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 75 144 3 10 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 75 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 144
  (Polychromatic418967fa.accept_21_7_12_18_1_3040 28 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 75 144 3 9 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 75 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 75 144 (Polychromatic418967fa.accept_19_6_18_11_1_7636 25 75
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 75 144 3 8 25 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 75 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 75 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 75 144 3 7 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 75 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 75 144
  (Polychromatic418967fa.accept_10_9_5_4_1_966 19 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 75 144 3 6 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 75 144 (Polychromatic418967fa.accept_13_4_10_1_1_1390 17 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 75 144 3 5 25 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 75 144
  (Polychromatic418967fa.accept_17_14_7_8_1_7544 14 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 75 144 3 4 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 75 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 144
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 75 144 3 3 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 75 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 75 144 (Polychromatic418967fa.accept_19_7_18_11_1_464 7 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 75 144 3 2 25 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 75 144
  (Polychromatic418967fa.accept_20_5_15_4_1_7635 5 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 75 144 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 75 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 75 144 3 1 25 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 75 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 75 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 75 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 75 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 74 144 (Eq.refl
  Bool.true) (allA_succ_of_gcd 70 74 144 2 35 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 74 144 (Polychromatic418967fa.accept_20_9_14_4_1_4540 69 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 144 2 34 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 144 (accept_3_4 67 74 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 144 2 33 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 144 (Polychromatic418967fa.accept_15_5_14_9_1_274
  65 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 144 2 32 37 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 144
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 144 2 31 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 144 (accept_3_4 61 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  144 2 30 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 59 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 144 2 29 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 144 (Polychromatic418967fa.accept_13_5_9_1_1_1405 57 74 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 144 2 28 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 144 (accept_3_4 55 74 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 144 2 27 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 144
  (Polychromatic418967fa.accept_15_8_14_9_1_4216 53 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 144 2 26 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 74 144 (Polychromatic418967fa.accept_15_6_14_9_1_1471 51 74 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 144 2 25 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 144 (accept_3_4 49 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 144 2 24 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 144 (Polychromatic418967fa.accept_13_8_9_1_1_2147 47 74 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 144 2 23 37 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 144
  (Polychromatic418967fa.accept_13_6_9_1_1_5604 45 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 144 2 22 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 144 (accept_3_4 43 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  144 2 21 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 144 (Polychromatic418967fa.accept_13_2_9_1_1_67 41 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 144 2 20 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 144 (Polychromatic418967fa.accept_20_19_14_4_1_7634 39 74 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 144 2 19 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 144 (accept_3_4 37 74 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 144 2 18 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 144
  (Polychromatic418967fa.accept_15_5_14_9_1_274 35 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 144 2 17 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 144 (Polychromatic418967fa.accept_19_14_17_11_1_7501 33 74 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 144 2 16 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 144 (accept_3_4 31 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 144 2 15 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 144 (Polychromatic418967fa.accept_20_9_14_4_1_4540 29 74 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 144 2 14 37 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 144
  (Polychromatic418967fa.accept_15_12_14_9_1_778 27 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 144 2 13 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 74 144 (accept_3_4 25 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74
  144 2 12 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 144 (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 144 2 11 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 74 144 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 74 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 144 2 10 37 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 144 (accept_3_4 19 74 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 144 2 9 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 144
  (Polychromatic418967fa.accept_25_17_24_19_1_7633 17 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 74 144 2 8 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 74 144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 15 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 144 2 7 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 144 (accept_3_4 13 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 144 2 6 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 74 144 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 74 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 144 2 5 37 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 144
  (Polychromatic418967fa.accept_17_9_6_8_1_6315 9 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 144 2 4 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 144 (accept_3_4 7 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 144
  2 3 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  144 (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 74 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 74 144 2 2 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 74 144 (Polychromatic418967fa.accept_20_3_14_4_1_7632 3 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 144 2 1 37 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 144 (accept_3_4 1 74 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 74 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 72 73 144 (Eq.refl Bool.true) (allA_succ_of_accept 71 73 144 (accept_3_5 71 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 73 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 70 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 73 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 69 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 73 144 (accept_3_5 68 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67
  73 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 67 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 73 144 (Polychromatic418967fa.accept_21_3_10_18_1_7631 66 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 73 144 (accept_3_5 65 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 73 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 64 73 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 73 144
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 73 144 (accept_3_5 62 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  73 144 (Polychromatic418967fa.accept_11_6_7_1_1_564 61 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 73 144 (Polychromatic418967fa.accept_22_16_7_12_1_7630 60 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 73 144 (accept_3_5 59 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 73 144 (Polychromatic418967fa.accept_13_6_8_1_1_2913 58 73 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 73 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 73 144 (accept_3_5 56 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  73 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 73 144 (Polychromatic418967fa.accept_17_3_5_8_1_1687 54 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 73 144 (accept_3_5 53 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 73 144 (Polychromatic418967fa.accept_15_7_13_9_1_1466 52 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 73 144
  (Polychromatic418967fa.accept_13_12_8_1_1_825 51 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 73 144 (accept_3_5 50 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  73 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 49 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 73 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 73 144 (accept_3_5 47 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 73 144 (Polychromatic418967fa.accept_13_7_8_1_1_2145 46 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 73 144
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 73 144 (accept_3_5 44 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  73 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 73 144 (Polychromatic418967fa.accept_19_4_16_11_1_6046 42 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 73 144 (accept_3_5 41 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 73 144 (Polychromatic418967fa.accept_19_2_16_11_1_6045 40 73
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 73 144
  (Polychromatic418967fa.accept_10_9_3_4_1_985 39 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 73 144 (accept_3_5 38 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  73 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 37 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 73 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 73 144 (accept_3_5 35 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 73 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 73 144
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 33 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 73 144 (accept_3_5 32 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  73 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 73 144 (Polychromatic418967fa.accept_17_13_5_8_1_896 30 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 73 144 (accept_3_5 29 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 73 144 (Polychromatic418967fa.accept_11_6_7_1_1_564 28 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 73 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 27 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 73 144 (accept_3_5 26 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  73 144 (Polychromatic418967fa.accept_13_12_8_1_1_825 25 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 73 144 (Polychromatic418967fa.accept_13_11_8_1_1_3815 24 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 73 144 (accept_3_5 23 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 73 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 73 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 73 144
  (Polychromatic418967fa.accept_14_7_3_4_1_1816 21 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 73 144 (accept_3_5 20 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  73 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 19 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 73 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 73 144 (accept_3_5 17 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 73 144 (Polychromatic418967fa.accept_22_16_7_12_1_7630 16 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 73 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 15 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 73 144 (accept_3_5 14 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  73 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 73 144 (Polychromatic418967fa.accept_13_12_8_1_1_825 12 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 73 144 (accept_3_5 11 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 73 144 (Polychromatic418967fa.accept_22_10_7_12_1_7629 10 73 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 73 144
  (Polychromatic418967fa.accept_10_9_3_4_1_985 9 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 73 144 (accept_3_5 8 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 73
  144 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 73 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 73 144 (accept_3_5 5 73 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 73 144 (Polychromatic418967fa.accept_15_4_13_9_1_3197 4 73 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 73 144 (Polychromatic418967fa.accept_15_3_13_9_1_3196
  3 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 73 144 (accept_3_5 2 73
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 73 144 (Polychromatic418967fa.accept_7_1_3_4_1_128
  1 73 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 73
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 72 144 (allA_succ_of_accept 71
  72 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 71 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 72 144 2 35 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 69 72 144 3 23 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 72 144 4 17 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 72 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 67 72 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 144 6 11 12 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 144
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 65 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 72 144 8 8 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 72 144 9 7 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 72 144 2 31 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 61 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72 144 12 5 6 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 72 144 (Polychromatic418967fa.accept_15_14_12_9_1_3216 59 72
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 72 144 2 29 36 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 72 144 3 19 24 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 72 144 8 7 9 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 55 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 72 144 18 3 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 72 144 (Polychromatic418967fa.accept_21_11_9_18_1_4429 53 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 72 144 4 13 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 72 144 3 17 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 72 144 2 25 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 49
  72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 144 24 2 3 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 72 144 2 23 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 72 144 9 5 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 44 72 144 4 11 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 144 (Polychromatic418967fa.accept_19_5_15_11_1_7568 43 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72 144 6 7 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 72 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 41 72 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 72 144 8 5 9 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 72 144 3 13 24 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 72 144 2 19 36 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 144
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 72 144 36 1 2 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 72 144 (Polychromatic418967fa.accept_15_5_12_9_1_2253 35 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 144 2 17 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 72 144 3 11 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 72 144 8 4 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 144 (Polychromatic418967fa.accept_21_10_9_18_1_7628
  31 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 144 6 5 12 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 144
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 72 144 4 7 18 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 72 144 9 3 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 72 144 2 13 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 72 144 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 144 24 1 3 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 144 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 72 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 144 2 11 36 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 72 144 3 7 24 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 72 144 4 5 18 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 72 144 18 1 4 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 72 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 144 8 2 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 72 144 3 5 24 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 72 144 2 7 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 72 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 144 12 1 6 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 72 144
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 72 144 2 5 36 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 72 144 9 1 8 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 72 144 8 1 9 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 72 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 144 6 1 12 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 72 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 144 4 1 18 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 72 144 3 1 24 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 72 144 2 1 36 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 144
  (Polychromatic418967fa.accept_17_1_4_8_1_5049 1 72 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 72 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 144
  (allA_succ_of_accept 70 71 144 (accept_3_4 70 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 144 (Polychromatic418967fa.accept_30_9_11_24_1_5305 69 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 68 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 144 (accept_3_4 67 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 66 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 144
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 65 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 144 (accept_3_4 64 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 144 (Polychromatic418967fa.accept_17_12_3_8_1_7627 63 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 144 (Polychromatic418967fa.accept_15_2_11_9_1_263 62 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 144 (accept_3_4 61 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 144 (Polychromatic418967fa.accept_13_8_6_1_1_3808 60 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 59 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 144 (accept_3_4 58 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 57 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 144 (Polychromatic418967fa.accept_17_5_3_8_1_1697 56 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 144 (accept_3_4 55 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 54 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 144
  (Polychromatic418967fa.accept_14_11_1_4_1_4445 53 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 144 (accept_3_4 52 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 144 (Polychromatic418967fa.accept_15_6_11_9_1_3215 51 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 50 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 144 (accept_3_4 49 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 144 (Polychromatic418967fa.accept_13_9_6_1_1_2902 48 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 144 (accept_3_4 46 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 144 (Polychromatic418967fa.accept_13_5_6_1_1_822 44 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 144 (accept_3_4 43 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 144 (Polychromatic418967fa.accept_13_3_6_1_1_3797 42 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 144
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 41 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 144 (accept_3_4 40 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 144 (accept_3_4 37 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 144 (Polychromatic418967fa.accept_15_6_11_9_1_3215 36 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 144
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 144 (accept_3_4 34 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 144 (Polychromatic418967fa.accept_15_2_11_9_1_263 32 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 144 (accept_3_4 31 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 144 (Polychromatic418967fa.accept_17_13_3_8_1_6310 30 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 144
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 144 (accept_3_4 28 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 144 (accept_3_4 25 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 144
  (Polychromatic418967fa.accept_22_1_5_12_1_7557 23 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 144 (accept_3_4 22 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 144 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 144 (Polychromatic418967fa.accept_13_7_6_1_1_368 20 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 144 (accept_3_4 19 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 144 (Polychromatic418967fa.accept_13_5_6_1_1_822 18 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 144 (accept_3_4 16 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 144 (Polychromatic418967fa.accept_25_14_21_19_1_7626 14 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 144 (accept_3_4 13 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 71 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 144
  (Polychromatic418967fa.accept_14_11_1_4_1_4445 11 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 144 (accept_3_4 10 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 144 (Polychromatic418967fa.accept_13_9_6_1_1_2902 9 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 144 (Polychromatic418967fa.accept_13_8_6_1_1_3808 8 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 144 (accept_3_4 7 71 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 71 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 144 (accept_3_4 4 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 71 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 144 (accept_3_4 1 71 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 144
  (allA_succ_of_accept 69 70 144 (Polychromatic418967fa.accept_13_4_5_1_1_833 69 70 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 70 144 2 34 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 70 144 (Polychromatic418967fa.accept_17_16_2_8_1_7625
  67 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 70 144 2 33 35 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 70 144 (accept_3_5 65
  70 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 70 144 2 32 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 70 144
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 63 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 70 144 2 31 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 70 144 (Polychromatic418967fa.accept_13_9_5_1_1_1382 61 70 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 70 144 2 30 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 70 144 (accept_3_5 59 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 58 70 144 2 29 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 70 144 (Polychromatic418967fa.accept_15_12_10_9_1_798 57 70 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 70 144 2 28 35 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 70 144
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 55 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 70 144 2 27 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 70 144 (accept_3_5 53 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 70
  144 2 26 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51
  70 144 (Polychromatic418967fa.accept_13_12_5_1_1_1383 51 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 70 144 2 25 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 70 144 (Polychromatic418967fa.accept_15_4_10_9_1_4298 49 70 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 70 144 2 24 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 70 144 (accept_3_5 47 70 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 70 144 2 23 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 70 144
  (Polychromatic418967fa.accept_13_6_5_1_1_834 45 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 70 144 2 22 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 70 144 (Polychromatic418967fa.accept_13_4_5_1_1_833 43 70 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 70 144 2 21 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 70 144 (accept_3_5 41 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 70 144 2 20 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 70 144 (Polychromatic418967fa.accept_25_14_20_19_1_7624 39 70
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 70 144 2 19 35 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 70 144
  (Polychromatic418967fa.accept_38_37_32_30_1_7623 37 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 70 144 2 18 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 70 144 (accept_3_5 35 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 70 144 2 17 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 70 144 (Polychromatic418967fa.accept_15_3_10_9_1_769 33 70 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 70 144 2 16 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 70 144 (Polychromatic418967fa.accept_15_1_10_9_1_1495
  31 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 70 144 2 15 35 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 70 144 (accept_3_5 29
  70 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 70 144 2 14 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 70 144
  (Polychromatic418967fa.accept_15_12_10_9_1_798 27 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 70 144 2 13 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 70 144 (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 70 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 70 144 2 12 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 70 144 (accept_3_5 23 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 22 70 144 2 11 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 70 144 (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 70 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 70 144 2 10 35 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 70 144
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 70 144 2 9 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 70 144 (accept_3_5 17 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 70
  144 2 8 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  70 144 (Polychromatic418967fa.accept_20_15_10_4_1_4571 15 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 70 144 2 7 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 70 144 (Polychromatic418967fa.accept_21_13_7_18_1_5966 13 70 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 70 144 2 6 35 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 70 144 (accept_3_5 11 70 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 70 144 2 5 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 70 144 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 70 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 70 144 2 4 35 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 70 144
  (Polychromatic418967fa.accept_19_7_13_11_1_1208 7 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 70 144 2 3 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 70 144 (accept_3_5 5 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 70 144
  2 2 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 70
  144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 70 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 70 144 2 1 35 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 70 144 (Polychromatic418967fa.accept_15_1_10_9_1_1495 1 70 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 70
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 69 144 (allA_succ_of_accept 68 69
  144 (Polychromatic418967fa.accept_7_5_6_4_1_117 68 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 144 (Polychromatic418967fa.accept_19_10_12_11_1_7622 67 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 69 144 3 22 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 69 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 65
  69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 144
  (Polychromatic418967fa.accept_19_7_12_11_1_7621 64 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 69 144 3 21 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 69 144 (Polychromatic418967fa.accept_13_10_4_1_1_2142 62 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 69 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 61 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 69 144 3 20 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 69 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 69 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 58 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 69 144 3 19 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 69 144
  (Polychromatic418967fa.accept_19_18_12_11_1_3386 56 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 69 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 55 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 69 144 3 18 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 69 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 53 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 69 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 69 144 3 17 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 69 144 (Polychromatic418967fa.accept_27_23_15_9_1_7620
  50 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 69 144
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 69 144 3 16 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 69 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 46 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 69 144 3 15 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 69 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 44 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 43 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 69 144 3 14 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 69 144 (Polychromatic418967fa.accept_17_7_1_8_1_6280
  41 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 40 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 69 144 3 13 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 69 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 69 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 69 144 3 12 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 69 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 69 144 (Polychromatic418967fa.accept_20_14_9_4_1_7517 34 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 69 144 3 11 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 69 144
  (Polychromatic418967fa.accept_19_13_12_11_1_1249 32 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 69 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 69 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 69 144 3 10 23 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 69 144
  (Polychromatic418967fa.accept_13_3_4_1_1_363 29 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 69 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 69 144 3 9 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 69 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 69 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 69 144 3 8 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 69 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 144 (Polychromatic418967fa.accept_19_3_12_11_1_7619 22 69
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 69 144 3 7 23 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 69 144
  (Polychromatic418967fa.accept_19_1_12_11_1_1245 20 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 69 144 3 6 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 69 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 16 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 69 144 3 5 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 69 144 (Polychromatic418967fa.accept_20_14_9_4_1_7517 14 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 69 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 69 144 3 4 23 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 69 144
  (Polychromatic418967fa.accept_17_11_1_8_1_7502 11 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 69 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 69 144 3 3 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 69 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 69 144
  (Polychromatic418967fa.accept_17_7_1_8_1_6280 7 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 69 144 3 2 23 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 69 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 144 (Polychromatic418967fa.accept_17_4_1_8_1_5070 4 69 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 69 144 3 1 23 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 69 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 2 69 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 69 144 (Polychromatic418967fa.accept_19_1_12_11_1_1245 1 69 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 69 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 68 144 (allA_succ_of_accept 67 68 144 (accept_3_4 67 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 68 144 2 33 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 68 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 65 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 68 144 4 16 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 68 144 (Polychromatic418967fa.accept_13_11_3_1_1_1397
  63 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 144 2 31 34 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 144 (accept_3_4 61
  68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 144 4 15 17 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 144
  (Polychromatic418967fa.accept_10_9_8_4_1_970 59 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 68 144 2 29 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 68 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 68 144 4 14 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 68 144 (accept_3_4 55 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68 144 2 27 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 68 144 (Polychromatic418967fa.accept_21_11_5_18_1_5998 53 68
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 68 144 4 13 17 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 68 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 51 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 68 144 2 25 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 68 144 (accept_3_4 49 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68
  144 4 12 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  68 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 47 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 68 144 2 23 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 68 144 (Polychromatic418967fa.accept_13_6_3_1_1_1413 45 68 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 144 4 11 17 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 144 (accept_3_4 43 68 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 144 2 21 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 41 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 68 144 4 10 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 68 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 68 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 68 144 2 19 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 68 144 (accept_3_4 37 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68 144 4 9 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 68 144 (Polychromatic418967fa.accept_21_14_5_18_1_7618 35 68 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 68 144 2 17 34 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 68 144
  (Polychromatic418967fa.accept_13_7_3_1_1_814 33 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 68 144 4 8 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 68 144 (accept_3_4 31 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68
  144 2 15 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  68 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 68 144 4 7 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 68 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 144 2 13 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 144 (accept_3_4 25 68 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 144 4 6 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 68 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 144 2 11 34 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 144
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 144 4 5 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 144 (accept_3_4 19 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  144 2 9 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 144 (Polychromatic418967fa.accept_13_4_3_1_1_2898 17 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 144 4 4 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 144 2 7 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 144 (accept_3_4 13 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 144 4 3 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 144 (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 68 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 144 2 5 34 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 9 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 144 4 2 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 144 (accept_3_4 7 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 144
  2 3 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  144 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 68 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 68 144 4 1 17 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 68 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 144 2 1 34 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 144 (accept_3_4 1 68 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 68 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  67 144 (allA_succ_of_accept 66 67 144 (Polychromatic418967fa.accept_21_3_4_18_1_7617 66 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 67 144 (accept_3_5 65 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 67 144 (Polychromatic418967fa.accept_13_12_2_1_1_2909 64 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 67 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 63 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 67 144 (accept_3_5 62 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61
  67 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 61 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 67 144 (Polychromatic418967fa.accept_17_9_16_8_1_2721 60 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 67 144 (accept_3_5 59 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 67 144 (Polychromatic418967fa.accept_13_6_2_1_1_2137 58 67 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 67 144
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 57 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 67 144 (accept_3_5 56 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55
  67 144 (Polychromatic418967fa.accept_13_3_2_1_1_2907 55 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 67 144 (Polychromatic418967fa.accept_21_12_4_18_1_4424 54 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 67 144 (accept_3_5 53 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 67 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 67 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 67 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 51 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 67 144 (accept_3_5 50 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49
  67 144 (Polychromatic418967fa.accept_14_7_11_4_1_3455 49 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 67 144 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 67 144 (accept_3_5 47 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 67 144 (Polychromatic418967fa.accept_15_1_7_9_1_20 46 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 67 144
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 45 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 67 144 (accept_3_5 44 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43
  67 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 43 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 67 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 67 144 (accept_3_5 41 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 67 144 (Polychromatic418967fa.accept_19_2_10_11_1_7616 40 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 67 144
  (Polychromatic418967fa.accept_19_1_10_11_1_4721 39 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 67 144 (accept_3_5 38 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37
  67 144 (Polychromatic418967fa.accept_19_18_10_11_1_6058 37 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 67 144 (Polychromatic418967fa.accept_14_8_11_4_1_3438 36 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 67 144 (accept_3_5 35 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 67 144 (Polychromatic418967fa.accept_19_15_10_11_1_4735 34 67
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 67 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 33 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 67 144 (accept_3_5 32 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31
  67 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 31 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 67 144 (Polychromatic418967fa.accept_21_9_4_18_1_7615 30 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 67 144 (accept_3_5 29 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 67 144 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 67
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 67 144
  (Polychromatic418967fa.accept_19_8_10_11_1_7614 27 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 67 144 (accept_3_5 26 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25
  67 144 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 67 144 (Polychromatic418967fa.accept_17_7_16_8_1_7613 24 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 67 144 (accept_3_5 23 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 67 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 67 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 67 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 21 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 67 144 (accept_3_5 20 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19
  67 144 (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 67 144 (Polychromatic418967fa.accept_19_18_10_11_1_6058 18 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 67 144 (accept_3_5 17 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 67 144 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 67 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 67 144
  (Polychromatic418967fa.accept_14_1_11_4_1_3430 15 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 67 144 (accept_3_5 14 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13
  67 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 67 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 67 144 (accept_3_5 11 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 67 144 (Polychromatic418967fa.accept_29_10_9_28_1_7612 10 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 67 144
  (Polychromatic418967fa.accept_13_9_2_1_1_813 9 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 67 144 (accept_3_5 8 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 67
  144 (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 67 144 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 67 144 (accept_3_5 5 67 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 67 144 (Polychromatic418967fa.accept_22_4_1_12_1_7611 4 67 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 67 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 3 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 67 144 (accept_3_5 2 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 67
  144 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 67 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 67 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 66 144
  (allA_succ_of_accept 65 66 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 65 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 66 144 2 32 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 66 144 3 21 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 66 144 2 31 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 61
  66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 144 6 10 11 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 144
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 59 66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 66 144 2 29 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 66 144 3 19 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 66 144 2 28 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 55 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66 144 6 9 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 66 144 (Polychromatic418967fa.accept_19_15_9_11_1_7514 53 66
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 66 144 2 26 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 66 144 3 17 22 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 66 144 2 25 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 144
  (Polychromatic418967fa.accept_14_7_10_4_1_130 49 66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 66 144 6 8 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 66 144 (Polychromatic418967fa.accept_17_13_15_8_1_3860 47 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 66 144 2 23 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 66 144 3 15 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 66 144 2 22 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 43
  66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 144 6 7 11 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 144 2 20 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 66 144 3 13 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 66 144 2 19 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 144 (Polychromatic418967fa.accept_21_16_3_18_1_7610 37 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 144 6 6 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 66 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 144 2 17 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 66 144 3 11 22 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 66 144 2 16 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 144
  (Polychromatic418967fa.accept_15_1_6_9_1_254 31 66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 66 144 6 5 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 66 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 66 144 2 14 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 66 144 3 9 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 66 144 2 13 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 25
  66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 144 6 4 11 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 144
  (Polychromatic418967fa.accept_17_6_15_8_1_1714 23 66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 144 2 11 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 66 144 3 7 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 66 144 2 10 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 144 (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 144 6 3 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 66 144 (Polychromatic418967fa.accept_19_17_9_11_1_6057 17 66
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 144 2 8 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 66 144 3 5 22 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 66 144 2 7 33 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 66 144 6 2 11 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 66 144 (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 144 2 5 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 66 144 3 3 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 66 144 2 4 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 144 (Polychromatic418967fa.accept_14_7_10_4_1_130 7 66 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 144 6 1 11 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66 144
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 66 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 144 2 2 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 66 144 3 1 22 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 66 144 2 1 33 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 66 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 66 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 65 144 (allA_succ_of_accept 64 65 144 (accept_3_4 64 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 65 144 (Polychromatic418967fa.accept_15_3_5_9_1_764 63 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 65 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 62 65 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 144 (accept_3_4 61 65 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 144 (Polychromatic418967fa.accept_19_3_8_11_1_7609
  60 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 144
  (Polychromatic418967fa.accept_10_9_5_4_1_966 59 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 144 (accept_3_4 58 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017 57 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 144 (accept_3_4 55 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 54 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 144
  (Polychromatic418967fa.accept_11_9_10_1_1_581 53 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 144 (accept_3_4 52 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 144 (Polychromatic418967fa.accept_17_16_14_8_1_7608 50 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 144 (accept_3_4 49 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 48 65 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 47 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 144 (accept_3_4 46 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 144 (Polychromatic418967fa.accept_17_11_14_8_1_2729 45 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 144 (Polychromatic418967fa.accept_14_2_9_4_1_1735 44 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 144 (accept_3_4 43 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 144 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 144 (accept_3_4 40 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 144 (Polychromatic418967fa.accept_25_13_15_19_1_7607 38 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 144 (accept_3_4 37 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 65 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 144
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 144 (accept_3_4 34 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 144 (Polychromatic418967fa.accept_23_9_19_6_1_7606 32 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 144 (accept_3_4 31 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 144 (Polychromatic418967fa.accept_14_2_9_4_1_1735 30 65 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 144
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 144 (accept_3_4 28 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 144 (accept_3_4 25 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 144
  (Polychromatic418967fa.accept_17_6_14_8_1_3858 23 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 144 (accept_3_4 22 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 144 (accept_3_4 19 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 144 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 144
  (Polychromatic418967fa.accept_19_17_8_11_1_7605 17 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 144 (accept_3_4 16 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 144 (Polychromatic418967fa.accept_20_15_5_4_1_4566 15 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 144 (Polychromatic418967fa.accept_15_14_5_9_1_2284 14 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 144 (accept_3_4 13 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 65 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 144
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 144 (accept_3_4 10 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 144 (Polychromatic418967fa.accept_22_8_21_12_1_7604 8 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 144 (accept_3_4 7 65 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 65 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 144 (accept_3_4 4 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  144 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 65 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 144 (accept_3_4 1 65 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 144
  (allA_succ_of_accept 63 64 144 (Polychromatic418967fa.accept_13_11_12_1_1_2154 63 64 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 64 144 2 31 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 64 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 61
  64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 64 144 4 15 16 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 64 144 (accept_3_5 59
  64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 64 144 2 29 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 64 144
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 57 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 64 144 8 7 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 64 144 (Polychromatic418967fa.accept_15_10_4_9_1_3203 55 64 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 64 144 2 27 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 64 144 (accept_3_5 53 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 64 144 4 13 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 64 144 (Polychromatic418967fa.accept_15_6_4_9_1_1438 51 64 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 64 144 2 25 32 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 64 144
  (Polychromatic418967fa.accept_17_15_13_8_1_7603 49 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 64 144 16 3 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 64 144 (accept_3_5 47 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 64
  144 2 23 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  64 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 64 144 4 11 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 64 144 (Polychromatic418967fa.accept_11_10_9_1_1_2186 43 64 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 64 144 2 21 32 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 64 144 (accept_3_5 41 64 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 64 144 8 5 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 64 144 (Polychromatic418967fa.accept_14_11_8_4_1_2628
  39 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 64 144 2 19 32 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 64 144
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 37 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 64 144 4 9 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 64 144 (accept_3_5 35 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 64
  144 2 17 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  64 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 64 144 16 2 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 64 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 64 144 2 15 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 64 144 (accept_3_5 29 64 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 64 144 4 7 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 64 144 (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 64 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 64 144 2 13 32 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 64 144
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 25 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 64 144 8 3 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 64 144 (accept_3_5 23 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 64
  144 2 11 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  64 144 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 64 144 4 5 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 64 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 64 144 2 9 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 64 144 (accept_3_5 17 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 64 144 16 1 4 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 64 144 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 64 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 64 144 2 7 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 64 144
  (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 64 144 4 3 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 64 144 (accept_3_5 11 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 64
  144 2 5 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  64 144 (Polychromatic418967fa.accept_19_9_7_11_1_7602 9 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 64 144 8 1 8 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 64 144 (Polychromatic418967fa.accept_25_7_14_19_1_7601 7 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 64 144 2 3 32 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 64 144 (accept_3_5 5 64 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 64 144 4 1 16 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 64 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 64 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 64 144 2 1 32 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 64 144
  (Polychromatic418967fa.accept_22_1_20_12_1_2869 1 64 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 64 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 63 144
  (allA_succ_of_accept 62 63 144 (Polychromatic418967fa.accept_13_10_11_1_1_2152 62 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 63 144 (Polychromatic418967fa.accept_13_9_11_1_1_1375 61 63
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 63 144 3 20 21 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 63 144
  (Polychromatic418967fa.accept_10_9_3_4_1_985 59 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 63 144 (Polychromatic418967fa.accept_15_13_3_9_1_1482 58 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 63 144 3 19 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 63 144 (Polychromatic418967fa.accept_17_5_12_8_1_6304
  56 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 63 144
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 55 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 63 144 9 6 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 63 144 (Polychromatic418967fa.accept_14_11_7_4_1_3449 53 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 144 (Polychromatic418967fa.accept_14_10_7_4_1_3453 52 63
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 63 144 3 17 21 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 63 144
  (Polychromatic418967fa.accept_15_5_3_9_1_283 50 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 49 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 63 144 3 16 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 63 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 47
  63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 144
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 46 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 63 144 9 5 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 63 144 (Polychromatic418967fa.accept_17_10_12_8_1_2748 44 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 63 144 (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 63
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 63 144 3 14 21 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 63 144
  (Polychromatic418967fa.accept_20_1_3_4_1_3213 41 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 63 144 (Polychromatic418967fa.accept_15_10_3_9_1_3285 40 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 63 144 3 13 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 63 144 (Polychromatic418967fa.accept_13_12_11_1_1_2920
  38 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 63 144
  (Polychromatic418967fa.accept_10_7_3_4_1_978 37 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 63 144 9 4 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 63 144 (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 144 (Polychromatic418967fa.accept_13_8_11_1_1_3789 34 63
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 63 144 3 11 21 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 63 144
  (Polychromatic418967fa.accept_19_13_6_11_1_7600 32 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 144 (Polychromatic418967fa.accept_14_3_7_4_1_118 31 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 63 144 3 10 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 63 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 29
  63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 144
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 63 144 9 3 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 63 144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 26 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 63 144 (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 63
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 63 144 3 8 21 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 63 144
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 63 144 (Polychromatic418967fa.accept_13_9_11_1_1_1375 22 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 63 144 3 7 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 63 144 (Polychromatic418967fa.accept_13_7_11_1_1_2903 20 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 63 144
  (Polychromatic418967fa.accept_10_9_3_4_1_985 19 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 63 144 9 2 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 63 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 144 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 63
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 63 144 3 5 21 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 63 144
  (Polychromatic418967fa.accept_19_14_6_11_1_7599 14 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 144 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 63 144 3 4 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 63 144 (Polychromatic418967fa.accept_14_11_7_4_1_3449 11 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 144
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 63 144 9 1 7 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 63 144 (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 63 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 63 144 3 2 21 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 63 144
  (Polychromatic418967fa.accept_15_5_3_9_1_283 5 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 63 144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 63 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 63 144 3 1 21 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 63 144 (Polychromatic418967fa.accept_22_2_19_12_1_7598 2 63 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 144
  (Polychromatic418967fa.accept_19_1_6_11_1_7548 1 63 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 63 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 144 (allA_succ_of_accept
  61 62 144 (accept_3_4 61 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 144 2 30 31 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 59 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 144 2 29 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 57 62 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 144 2 28 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 144 (accept_3_4 55 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 144 2 27 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 144 (Polychromatic418967fa.accept_15_8_2_9_1_3200 53 62 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 144 2 26 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 51 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 144 2 25 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 144 (accept_3_4 49 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  144 2 24 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 144 2 23 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 62 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 144 2 22 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 144 (accept_3_4 43 62 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 144 2 21 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 144
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 41 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 144 2 20 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 144 (Polychromatic418967fa.accept_11_6_7_1_1_564 39 62 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 144 2 19 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 144 (accept_3_4 37 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 144 2 18 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 144 (Polychromatic418967fa.accept_13_9_10_1_1_1389 35 62 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 144 2 17 31 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 144 2 16 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 144 (accept_3_4 31 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  144 2 15 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 144 (Polychromatic418967fa.accept_19_10_5_11_1_7597 29 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 144 2 14 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 62 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 144 2 13 31 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 144 (accept_3_4 25 62 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 144 2 12 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 144 2 11 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 144 (Polychromatic418967fa.accept_25_21_12_19_1_7596 21 62 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 144 2 10 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 144 (accept_3_4 19 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 144 2 9 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 62 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 144 2 8 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 144
  (Polychromatic418967fa.accept_19_15_5_11_1_4719 15 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 144 2 7 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 144 (accept_3_4 13 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  144 2 6 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 144 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 144 2 5 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 144 2 4 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 144 (accept_3_4 7 62 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 144 2 3 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 62 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 144 2 2 31 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 3 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 144 2 1 31 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 144 (accept_3_4 1 62 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 144 (allA_succ_of_accept 60 61 144
  (Polychromatic418967fa.accept_11_5_6_1_1_988 60 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 61 144 (accept_3_5 59 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58
  61 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 58 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 61 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 57 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 61 144 (accept_3_5 56 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 61 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 55 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 61 144
  (Polychromatic418967fa.accept_13_2_9_1_1_67 54 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 61 144 (accept_3_5 53 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  61 144 (Polychromatic418967fa.accept_15_7_1_9_1_1500 52 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 61 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 51 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 61 144 (accept_3_5 50 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 61 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 49 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 61 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 48 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 61 144 (accept_3_5 47 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  61 144 (Polychromatic418967fa.accept_17_12_10_8_1_5039 46 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 61 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 61 144 (accept_3_5 44 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 61 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 43 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 61 144
  (Polychromatic418967fa.accept_22_20_17_12_1_7595 42 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 61 144 (accept_3_5 41 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 61 144 (Polychromatic418967fa.accept_11_7_6_1_1_2182 40 61 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 61 144 (Polychromatic418967fa.accept_26_13_9_14_1_7594 39 61
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 61 144 (accept_3_5 38 61 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 61 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 37
  61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 61 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 36 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 61 144 (accept_3_5 35 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  61 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 34 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 61 144 (Polychromatic418967fa.accept_21_12_19_18_1_7593 33 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 61 144 (accept_3_5 32 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 61 144 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 61 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 61 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 30 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 61 144 (accept_3_5 29 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  61 144 (Polychromatic418967fa.accept_13_2_9_1_1_67 28 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 61 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 61 144 (accept_3_5 26 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 61 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 61 144
  (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 61 144 (accept_3_5 23 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  61 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 61 144 (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 61 144 (accept_3_5 20 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 61 144 (Polychromatic418967fa.accept_13_6_9_1_1_5604 19 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 61 144
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 18 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 61 144 (accept_3_5 17 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  61 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 61 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 61 144 (accept_3_5 14 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 61 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 61 144
  (Polychromatic418967fa.accept_17_12_10_8_1_5039 12 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 61 144 (accept_3_5 11 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  61 144 (Polychromatic418967fa.accept_13_10_9_1_1_5609 10 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 61 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 61 144 (accept_3_5 8 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 61 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 61 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 61 144 (accept_3_5 5 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 61
  144 (Polychromatic418967fa.accept_21_4_19_18_1_7542 4 61 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 61 144 (Polychromatic418967fa.accept_19_3_4_11_1_469 3 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 61 144 (accept_3_5 2 61 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 61 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 61 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 61
  144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 60 144 (allA_succ_of_accept 59 60 144
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 59 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 144 2 29 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 60 144 3 19 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 60 144 4 14 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 60 144 (Polychromatic418967fa.accept_23_9_14_6_1_7592 55 60 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 144 6 9 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 144 (Polychromatic418967fa.accept_25_3_10_19_1_7591 53 60
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 144 4 13 15 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 60 144 3 17 20 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 60 144 2 25 30 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 60 144
  (Polychromatic418967fa.accept_22_5_16_12_1_7590 49 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 60 144 12 4 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 60 144 (Polychromatic418967fa.accept_19_9_3_11_1_7505 47 60 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 60 144 2 23 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 60 144 3 15 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 60 144 4 11 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 144 (Polychromatic418967fa.accept_23_20_14_6_1_7589
  43 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 144 6 7 10 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 144
  (Polychromatic418967fa.accept_22_19_16_12_1_7588 41 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 60 144 4 10 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 39 60 144 3 13 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 60 144 2 19 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 60 144 (Polychromatic418967fa.accept_13_11_8_1_1_3815 37 60 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 144 12 3 5 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 144
  (Polychromatic418967fa.accept_13_9_8_1_1_824 35 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 60 144 2 17 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 60 144 3 11 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 60 144 4 8 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 31 60 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60 144 6 5 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 60 144 (Polychromatic418967fa.accept_19_10_3_11_1_7587 29 60
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 60 144 4 7 15 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 60 144 3 9 20 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 60 144 2 13 30 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 144
  (Polychromatic418967fa.accept_13_12_8_1_1_825 25 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 60 144 12 2 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 60 144 (Polychromatic418967fa.accept_17_6_9_8_1_6316 23 60 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 144 2 11 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 60 144 3 7 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 60 144 4 5 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 144 (Polychromatic418967fa.accept_13_6_8_1_1_2913
  19 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 144 6 3 10 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 60 144
  (Polychromatic418967fa.accept_11_6_5_1_1_586 17 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 60 144 4 4 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 60 144 3 5 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 60 144 2 7 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 144 (Polychromatic418967fa.accept_19_13_3_11_1_4706 13 60 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 144 12 1 5 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 60 144 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 60 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 144 2 5 30 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 60 144 3 3 20 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 60 144 4 2 15 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 144
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 60 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 60 144 6 1 10 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 60 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 60 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 144 4 1 15 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 60 144 3 1 20 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 60 144 2 1 30 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 144 (Polychromatic418967fa.accept_17_1_9_8_1_7492 1 60 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 144 (allA_succ_of_accept 58 59 144
  (accept_3_4 58 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 57 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 144 (Polychromatic418967fa.accept_21_14_17_18_1_7586 56 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 144 (accept_3_4 55 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 144 (Polychromatic418967fa.accept_19_16_2_11_1_4705 54 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 53 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 144 (accept_3_4 52 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 144 (Polychromatic418967fa.accept_15_6_14_9_1_1471 51 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 50 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 144 (accept_3_4 49 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 48 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 144
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 47 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 144 (accept_3_4 46 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 144 (Polychromatic418967fa.accept_23_21_13_6_1_7585 44 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 144 (accept_3_4 43 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 144 (Polychromatic418967fa.accept_13_3_7_1_1_334 42 59 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 41 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 144 (accept_3_4 40 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 144 (Polychromatic418967fa.accept_23_16_13_6_1_7584 39 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 144 (accept_3_4 37 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 36 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 144 (accept_3_4 34 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 144 (Polychromatic418967fa.accept_13_6_7_1_1_335 32 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 144 (accept_3_4 31 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 144 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 144 (accept_3_4 28 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 144 (Polychromatic418967fa.accept_27_26_5_9_1_7583 26 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 144 (accept_3_4 25 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 144 (Polychromatic418967fa.accept_13_11_7_1_1_1386 24 59
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 23 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 144 (accept_3_4 22 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 144 (Polychromatic418967fa.accept_13_8_7_1_1_1385 21 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 144 (accept_3_4 19 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 144
  (Polychromatic418967fa.accept_23_17_13_6_1_7582 17 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 144 (accept_3_4 16 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 144 (Polychromatic418967fa.accept_20_14_19_4_1_7534 14 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 144 (accept_3_4 13 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 144 (Polychromatic418967fa.accept_15_12_14_9_1_778 12 59
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 144
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 144 (accept_3_4 10 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 144 (Polychromatic418967fa.accept_19_9_2_11_1_7581 9 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 59 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 8 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 144 (accept_3_4 7 59 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 59 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 144 (accept_3_4 4 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  144 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 59 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 144 (Polychromatic418967fa.accept_20_2_19_4_1_3246 2 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 144 (accept_3_4 1 59 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 144
  (allA_succ_of_accept 57 58 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 57 58 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 58 144 2 28 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 58 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 55
  58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 58 144 2 27 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 58 144 (accept_3_5 53
  58 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 58 144 2 26 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 58 144
  (Polychromatic418967fa.accept_14_9_2_4_1_1814 51 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 58 144 2 25 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 58 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 49 58 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 58 144 2 24 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 58 144 (accept_3_5 47 58 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 58 144 2 23 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 58 144 (Polychromatic418967fa.accept_21_3_16_18_1_7500 45 58
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 58 144 2 22 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 58 144
  (Polychromatic418967fa.accept_25_18_8_19_1_7580 43 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 58 144 2 21 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 58 144 (accept_3_5 41 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 58
  144 2 20 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39
  58 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 58 144 2 19 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 58 144 (Polychromatic418967fa.accept_14_9_2_4_1_1814 37 58 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 58 144 2 18 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 58 144 (accept_3_5 35 58 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 58 144 2 17 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 58 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 58 144 2 16 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 58 144 (Polychromatic418967fa.accept_13_5_6_1_1_822 31 58 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 58 144 2 15 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 58 144 (accept_3_5 29 58 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 58 144 2 14 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 58 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 58 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 58 144 2 13 29 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 58 144
  (Polychromatic418967fa.accept_19_6_1_11_1_7579 25 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 58 144 2 12 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 58 144 (accept_3_5 23 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 58
  144 2 11 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  58 144 (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 58 144 2 10 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 58 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 58 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 58 144 2 9 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 58 144 (accept_3_5 17 58 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 58 144 2 8 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 58 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 58 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 58 144 2 7 29 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 58 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 58 144 2 6 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 58 144 (accept_3_5 11 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 58
  144 2 5 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  58 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 58 144 2 4 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 58 144 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 58 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 58 144 2 3 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 58 144 (accept_3_5 5 58 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 58 144 2 2 29 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 58 144 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 58 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 58 144 2 1 29 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 58 144
  (Polychromatic418967fa.accept_17_1_7_8_1_6347 1 58 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 58 144)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 57 144 (allA_succ_of_accept 56
  57 144 (Polychromatic418967fa.accept_13_4_5_1_1_833 56 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 57 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 55 57 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 57 144 3 18 19 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 57 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 53 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 57 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 52 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 57 144 3 17 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 57 144 (Polychromatic418967fa.accept_15_5_12_9_1_2253
  50 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 57 144
  (Polychromatic418967fa.accept_15_4_12_9_1_773 49 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 57 144 3 16 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 57 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 47 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 144 (Polychromatic418967fa.accept_25_21_7_19_1_7578 46 57
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 57 144 3 15 19 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 57 144
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 44 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 43 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 57 144 3 14 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 57 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 41
  57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 40 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 57 144 3 13 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 57 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 38 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 57 144 (Polychromatic418967fa.accept_21_16_15_18_1_3050 37 57
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 57 144 3 12 19 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 57 144
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 57 144 (Polychromatic418967fa.accept_13_8_5_1_1_1381 34 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 57 144 3 11 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 57 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 32
  57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 57 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 57 144 3 10 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 57 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 144 (Polychromatic418967fa.accept_21_7_15_18_1_7526 28 57
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 57 144 3 9 19 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 57 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 26 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 25 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 57 144 3 8 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 57 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 144
  (Polychromatic418967fa.accept_10_2_7_4_1_967 22 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 57 144 3 7 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 57 144 (Polychromatic418967fa.accept_15_5_12_9_1_2253 20 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 57 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 57 144 3 6 19 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 57 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 17 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 57 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 57 144 3 5 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 57 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 57 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 13 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 57 144 3 4 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 57 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 57 144 3 3 19 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 57 144
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 8 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 144 (Polychromatic418967fa.accept_20_7_17_4_1_3239 7 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 57 144 3 2 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 57 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 144
  (Polychromatic418967fa.accept_13_4_5_1_1_833 4 57 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 57 144 3 1 19 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 57 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 57 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 57 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57
  144))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 56 144 (allA_succ_of_accept 55 56 144
  (accept_3_4 55 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 56 144 2 27 28 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 56 144
  (Polychromatic418967fa.accept_21_11_14_18_1_7577 53 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 56 144 4 13 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 56 144 (Polychromatic418967fa.accept_15_6_11_9_1_3215 51 56 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 144 2 25 28 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 144 (accept_3_4 49 56 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 144 8 6 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 144 (Polychromatic418967fa.accept_15_2_11_9_1_263
  47 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 56 144 2 23 28 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 56 144
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 56 144 4 11 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 56 144 (accept_3_4 43 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56
  144 2 21 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  56 144 (Polychromatic418967fa.accept_19_3_18_11_1_6074 41 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 56 144 8 5 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 56 144 (Polychromatic418967fa.accept_19_1_18_11_1_4704 39 56 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 56 144 2 19 28 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 56 144 (accept_3_4 37 56 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56 144 4 9 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 56 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 35
  56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 56 144 2 17 28 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 56 144
  (Polychromatic418967fa.accept_21_12_14_18_1_3005 33 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 56 144 8 4 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 56 144 (accept_3_4 31 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 56 144 2 15 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 56 144 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 56 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 144 4 7 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 144 (Polychromatic418967fa.accept_19_8_18_11_1_3408 27 56
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 144 2 13 28 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 144 (accept_3_4 25
  56 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 144 8 3 7 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 144
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 56 144 2 11 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 56 144 (Polychromatic418967fa.accept_15_6_11_9_1_3215 21 56 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 144 4 5 14 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 144 (accept_3_4 19 56 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 56 144 2 9 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 56 144 (Polychromatic418967fa.accept_15_2_11_9_1_263 17 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 56 144 8 2 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 56 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 144 2 7 28 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 144 (accept_3_4 13
  56 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 144 4 3 14 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 144
  (Polychromatic418967fa.accept_21_11_14_18_1_7577 11 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 56 144 2 5 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 56 144 (Polychromatic418967fa.accept_21_9_14_18_1_7576 9 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 144 8 1 7 18 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 144 (accept_3_4 7 56 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 144 2 3 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 56 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 56 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 56 144 4 1 14 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 56 144
  (Polychromatic418967fa.accept_13_3_4_1_1_363 3 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 56 144 2 1 28 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 56 144 (accept_3_4 1 56 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 56
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 144 (allA_succ_of_accept 54 55 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 54 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 55 144 (accept_3_5 53 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52
  55 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 52 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 55 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 51 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 55 144 (accept_3_5 50 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 55 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 49 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 55 144
  (Polychromatic418967fa.accept_15_3_10_9_1_769 48 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 55 144 (accept_3_5 47 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46
  55 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 46 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 55 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 45 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 55 144 (accept_3_5 44 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 55 144 (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 55 144
  (Polychromatic418967fa.accept_15_12_10_9_1_798 42 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 55 144 (accept_3_5 41 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  55 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 40 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 55 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 55 144 (accept_3_5 38 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 55 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 55 144
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 55 144 (accept_3_5 35 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  55 144 (Polychromatic418967fa.accept_15_4_10_9_1_4298 34 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 55 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 55 144 (accept_3_5 32 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 55 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 55 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 30 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 55 144 (accept_3_5 29 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  55 144 (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 55 144 (Polychromatic418967fa.accept_15_12_10_9_1_798 27 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 55 144 (accept_3_5 26 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 55 144 (Polychromatic418967fa.accept_19_6_17_11_1_6039 25 55
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 55 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 24 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 55 144 (accept_3_5 23 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  55 144 (Polychromatic418967fa.accept_20_2_15_4_1_7575 22 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 55 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 55 144 (accept_3_5 20 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 55 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 55 144
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 55 144 (accept_3_5 17 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  55 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 55 144 (Polychromatic418967fa.accept_13_2_3_1_1_3823 15 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 55 144 (accept_3_5 14 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 55 144 (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 55 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 12 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 55 144 (accept_3_5 11 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  55 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 55 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 55 144 (accept_3_5 8 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 55 144 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 55 144
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 55 144 (accept_3_5 5 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 55
  144 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 55 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 55 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 55 144 (accept_3_5 2 55 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 55 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 55 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 55
  144))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 54 144 (allA_succ_of_accept 53 54 144
  (Polychromatic418967fa.accept_11_9_10_1_1_581 53 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 144 2 26 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 54 144 3 17 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 50 54 144 2 25 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 54 144 (Polychromatic418967fa.accept_20_9_14_4_1_4540 49 54 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 144 6 8 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 144 (Polychromatic418967fa.accept_17_13_3_8_1_6310 47 54 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 144 2 23 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 54 144 9 5 6 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 54 144 2 22 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 54 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 43 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 54 144 6 7 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 54 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 41 54 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 54 144 2 20 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 54 144 3 13 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 54 144 2 19 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 37
  54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 144 18 2 3 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 144
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 35 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 144 2 17 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 54 144 3 11 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 54 144 2 16 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 54 144 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 54 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 144 6 5 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 29 54 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 144 2 14 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 54 144 9 3 6 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 54 144 2 13 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 54 144
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 54 144 6 4 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 54 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 23 54 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 54 144 2 11 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 54 144 3 7 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 54 144 2 10 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 144 (Polychromatic418967fa.accept_13_6_2_1_1_2137
  19 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 144 18 1 3 8 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 144
  (Polychromatic418967fa.accept_26_17_2_14_1_7574 17 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 54 144 2 8 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 54 144 3 5 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 54 144 2 7 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 54 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54 144 6 2 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 54 144 (Polychromatic418967fa.accept_21_11_12_18_1_4455 11 54
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 54 144 2 5 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 54 144 9 1 6 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 54 144 2 4 27 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 144
  (Polychromatic418967fa.accept_21_7_12_18_1_3040 7 54 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 54 144 6 1 9 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 54 144 (Polychromatic418967fa.accept_17_5_3_8_1_1697 5 54 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 144 2 2 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 54 144 3 1 18 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 54 144 2 1 27 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 54 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 54 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  144)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 144 (allA_succ_of_accept 52 53 144 (accept_3_4
  52 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 144
  (Polychromatic418967fa.accept_20_11_13_4_1_7573 51 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 144 (Polychromatic418967fa.accept_14_8_11_4_1_3438 50 53 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 144 (accept_3_4 49 53 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 144 (Polychromatic418967fa.accept_15_3_8_9_1_795 48 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 144 (Polychromatic418967fa.accept_10_7_3_4_1_978
  47 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 144 (accept_3_4 46
  53 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 144
  (Polychromatic418967fa.accept_17_11_2_8_1_7569 45 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 144 (Polychromatic418967fa.accept_15_14_8_9_1_1452 44 53 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 144 (accept_3_4 43 53 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 144 (Polychromatic418967fa.accept_19_4_15_11_1_7498 42 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 144
  (Polychromatic418967fa.accept_21_20_11_18_1_3037 41 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 53 144 (accept_3_4 40 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 53 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 53 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 144 (Polychromatic418967fa.accept_25_13_3_19_1_7572 38 53
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 53 144 (accept_3_4 37 53 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 53 144 (Polychromatic418967fa.accept_14_8_11_4_1_3438
  36 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 53 144
  (Polychromatic418967fa.accept_14_7_11_4_1_3455 35 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 53 144 (accept_3_4 34 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  53 144 (Polychromatic418967fa.accept_15_3_8_9_1_795 33 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 53 144 (Polychromatic418967fa.accept_11_10_9_1_1_2186 32 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 53 144 (accept_3_4 31 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 53 144 (Polychromatic418967fa.accept_21_9_11_18_1_7571 30 53
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 53 144
  (Polychromatic418967fa.accept_10_9_3_4_1_985 29 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 53 144 (accept_3_4 28 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  53 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 53 144 (Polychromatic418967fa.accept_19_7_15_11_1_3420 26 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 53 144 (accept_3_4 25 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 53 144 (Polychromatic418967fa.accept_19_5_15_11_1_7568 24 53
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 53 144
  (Polychromatic418967fa.accept_19_4_15_11_1_7498 23 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 53 144 (accept_3_4 22 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  53 144 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 53 144 (Polychromatic418967fa.accept_19_1_15_11_1_4712 20 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 53 144 (accept_3_4 19 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 53 144 (Polychromatic418967fa.accept_15_3_8_9_1_795 18 53 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 53 144
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 53 144 (accept_3_4 16 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  53 144 (Polychromatic418967fa.accept_14_1_11_4_1_3430 15 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 53 144 (Polychromatic418967fa.accept_15_14_8_9_1_1452 14 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 53 144 (accept_3_4 13 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 53 144 (Polychromatic418967fa.accept_21_12_11_18_1_7570 12 53
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 53 144
  (Polychromatic418967fa.accept_17_11_2_8_1_7569 11 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 53 144 (accept_3_4 10 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  53 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 53 144 (Polychromatic418967fa.accept_14_8_11_4_1_3438 8 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 53 144 (accept_3_4 7 53 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 53 144 (Polychromatic418967fa.accept_19_6_15_11_1_4738 6 53 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 53 144
  (Polychromatic418967fa.accept_19_5_15_11_1_7568 5 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 53 144 (accept_3_4 4 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 53
  144 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 53 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 53 144 (Polychromatic418967fa.accept_15_2_8_9_1_4294 2 53 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 144 (accept_3_4 1 53 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 53 144))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 52 144
  (allA_succ_of_accept 51 52 144 (Polychromatic418967fa.accept_21_9_10_18_1_7567 51 52 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 52 144 2 25 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 52 144 (Polychromatic418967fa.accept_14_7_10_4_1_130
  49 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 52 144 4 12 13 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 52 144 (accept_3_5 47
  52 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 52 144 2 23 26 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 52 144
  (Polychromatic418967fa.accept_17_11_1_8_1_7502 45 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 52 144 4 11 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 52 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 52 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 52 144 2 21 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 52 144 (accept_3_5 41 52 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 40 52 144 4 10 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 52 144 (Polychromatic418967fa.accept_25_14_2_19_1_7566 39 52
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 52 144 2 19 26 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 52 144
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 52 144 4 9 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 52 144 (accept_3_5 35 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 52
  144 2 17 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33
  52 144 (Polychromatic418967fa.accept_22_11_8_12_1_1581 33 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 52 144 4 8 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 52 144 (Polychromatic418967fa.accept_15_1_7_9_1_20 31 52 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 52 144 2 15 26 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 52 144 (accept_3_5 29 52 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 52 144 4 7 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 52 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 52 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 52 144 2 13 26 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 52 144
  (Polychromatic418967fa.accept_19_6_14_11_1_7565 25 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 52 144 4 6 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 52 144 (accept_3_5 23 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 52
  144 2 11 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  52 144 (Polychromatic418967fa.accept_14_7_10_4_1_130 21 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 52 144 4 5 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 52 144 (Polychromatic418967fa.accept_28_19_24_4_1_7564 19 52 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 52 144 2 9 26 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 52 144 (accept_3_5 17 52 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 52 144 4 4 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 52 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 52 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 52 144 2 7 26 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 52 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 52 144 4 3 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 52 144 (accept_3_5 11 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 52
  144 2 5 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  52 144 (Polychromatic418967fa.accept_17_9_1_8_1_5045 9 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 52 144 4 2 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 52 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 52 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 52 144 2 3 26 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 52 144 (accept_3_5 5 52 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 52 144 4 1 13 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 52 144 (Polychromatic418967fa.accept_19_3_14_11_1_2214 3 52 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 52 144 2 1 26 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 52 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 1 52 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 52 144)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 51 144 (allA_succ_of_accept 50 51 144
  (Polychromatic418967fa.accept_11_6_7_1_1_564 50 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 51 144 (Polychromatic418967fa.accept_15_4_6_9_1_2269 49 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 51 144 3 16 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 51 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 47
  51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 144
  (Polychromatic418967fa.accept_15_1_6_9_1_254 46 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 51 144 3 15 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 51 144 (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 144 (Polychromatic418967fa.accept_19_5_13_11_1_6089 43 51
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 51 144 3 14 17 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 51 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 51 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 40 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 51 144 3 13 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 51 144 (Polychromatic418967fa.accept_21_17_9_18_1_7521
  38 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 144
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 37 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 51 144 3 12 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 51 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 51 144 3 11 17 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 51 144
  (Polychromatic418967fa.accept_21_11_9_18_1_4429 32 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 144 (Polychromatic418967fa.accept_13_5_12_1_1_2123 31 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 51 144 3 10 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 51 144 (Polychromatic418967fa.accept_15_14_6_9_1_2274
  29 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 144
  (Polychromatic418967fa.accept_11_6_7_1_1_564 28 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 51 144 3 9 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 51 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 26 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 51 144 3 8 17 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 51 144
  (Polychromatic418967fa.accept_27_23_24_9_1_7563 23 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 144 (Polychromatic418967fa.accept_19_3_13_11_1_2220 22 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 51 144 3 7 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 51 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 19 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 51 144 3 6 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 51 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 144 (Polychromatic418967fa.accept_14_2_9_4_1_1735 16 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 51 144 3 5 17 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 51 144
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 51 144 3 4 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 51 144 (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 51
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 144
  (Polychromatic418967fa.accept_20_10_11_4_1_7562 10 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 51 144 3 3 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 51 144 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 51 144 3 2 17 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 51 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 144 (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 51 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 51 144 3 1 17 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 51 144 (Polychromatic418967fa.accept_13_2_12_1_1_343 2 51 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 144
  (Polychromatic418967fa.accept_15_1_6_9_1_254 1 51 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 51 144))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 144 (allA_succ_of_accept 49 50 144
  (accept_3_4 49 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 144 2 24 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 47 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 144 2 23 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 50 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 45 50 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 144 2 22 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 144 (accept_3_4 43 50 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 144 2 21 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 144 (Polychromatic418967fa.accept_15_11_5_9_1_3205 41 50 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 144 2 20 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 144
  (Polychromatic418967fa.accept_14_11_8_4_1_2628 39 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 144 2 19 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 144 (accept_3_4 37 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50
  144 2 18 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  50 144 (Polychromatic418967fa.accept_13_9_11_1_1_1375 35 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 50 144 2 17 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 50 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 50 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 144 2 16 25 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 144 (accept_3_4 31 50 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 144 2 15 25 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 144
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 144 2 14 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 50 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 144 2 13 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 144 (accept_3_4 25 50 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 144 2 12 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 144 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 50
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 144 2 11 25 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 144
  (Polychromatic418967fa.accept_13_8_11_1_1_3789 21 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 144 2 10 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 144 (accept_3_4 19 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  144 2 9 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 144 2 8 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 50 144 (Polychromatic418967fa.accept_20_15_10_4_1_4571 15 50 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 144 2 7 25 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 144 (accept_3_4 13 50 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 144 2 6 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 50 144 (Polychromatic418967fa.accept_14_11_8_4_1_2628 11 50 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 144 2 5 25 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 144
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 50 144 2 4 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 50 144 (accept_3_4 7 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 144
  2 3 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50
  144 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 50 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 50 144 2 2 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 50 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 50 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 144 2 1 25 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 144 (accept_3_4 1 50 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 144)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 144 (allA_succ_of_accept
  48 49 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 49 144 (accept_3_5 47 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 49 144 (Polychromatic418967fa.accept_21_4_7_18_1_7561 46 49 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 49 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 49 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 49 144 (accept_3_5 44 49 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 49 144 (Polychromatic418967fa.accept_10_3_9_4_1_960
  43 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 49 144
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 42 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 49 144 (accept_3_5 41 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40
  49 144 (Polychromatic418967fa.accept_15_10_4_9_1_3203 40 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 49 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 39 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 49 144 (accept_3_5 38 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 49 144 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 49 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 49 144
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 49 144 (accept_3_5 35 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  49 144 (Polychromatic418967fa.accept_20_14_9_4_1_7517 34 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 49 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 33 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 49 144 (accept_3_5 32 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 49 144 (Polychromatic418967fa.accept_14_3_7_4_1_118 31 49 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 49 144
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 49 144 (accept_3_5 29 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  49 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 49 144 (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 49 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 49 144 (accept_3_5 26 49 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 49 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 49 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 49 144
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 24 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 49 144 (accept_3_5 23 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  49 144 (Polychromatic418967fa.accept_13_9_10_1_1_1389 22 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 49 144 (Polychromatic418967fa.accept_15_6_4_9_1_1438 21 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 49 144 (accept_3_5 20 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 49 144 (Polychromatic418967fa.accept_20_19_9_4_1_7560 19 49 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 49 144
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 49 144 (accept_3_5 17 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  49 144 (Polychromatic418967fa.accept_22_16_5_12_1_7559 16 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 49 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 49 144 (accept_3_5 14 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 49 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 13 49 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 49 144
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 49 144 (accept_3_5 11 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  49 144 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 49 144 (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 49 144 (accept_3_5 8 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 49 144 (Polychromatic418967fa.accept_22_7_5_12_1_7558 7 49 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 49 144
  (Polychromatic418967fa.accept_11_6_5_1_1_586 6 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 49 144 (accept_3_5 5 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 49
  144 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 49 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 49 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 49 144 (accept_3_5 2 49 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 49 144 (Polychromatic418967fa.accept_22_1_5_12_1_7557 1 49 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 49 144)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 48 144 (allA_succ_of_accept 47 48 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 47 48 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 144 2 23 24 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 48 144 3 15 16 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 48 144 4 11 12 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 144
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 48 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 48 144 6 7 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 48 144 (Polychromatic418967fa.accept_11_8_4_1_1_1000 41 48 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 144 8 5 6 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 48 144 3 13 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 48 144 2 19 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 37 48 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 144 12 3 4 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 144
  (Polychromatic418967fa.accept_15_5_3_9_1_283 35 48 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 144 2 17 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 48 144 3 11 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 48 144 16 2 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 48 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 48 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 144 6 5 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 48 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 144 4 7 12 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 48 144 3 9 16 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 48 144 2 13 24 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 48 144
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 48 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 48 144 24 1 2 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 48 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 23 48 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 48 144 2 11 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 48 144 3 7 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 48 144 4 5 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 19
  48 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 144 6 3 8 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 48 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 48 144 16 1 3 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 48 144 3 5 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 48 144 2 7 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 144 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 48 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48 144 12 1 4 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 48 144 (Polychromatic418967fa.accept_13_11_9_1_1_1407 11 48 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 48 144 2 5 24 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 48 144 3 3 16 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 48 144 8 1 6 18 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 144
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 7 48 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 48 144 6 1 8 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 48 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 48 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 144 4 1 12 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 48 144 3 1 16 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 48 144 2 1 24 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 48 144 (Polychromatic418967fa.accept_19_1_10_11_1_4721 1 48 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  144)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 144 (allA_succ_of_accept 46 47 144 (accept_3_4 46 47
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 144
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 45 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 47 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 44 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 47 144 (accept_3_4 43 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 47 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 47 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 47 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 41
  47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 144 (accept_3_4 40 47
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 144
  (Polychromatic418967fa.accept_17_5_13_8_1_7556 39 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 47 144 (Polychromatic418967fa.accept_13_12_8_1_1_825 38 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 47 144 (accept_3_4 37 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 47 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 36 47 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 47 144 (Polychromatic418967fa.accept_11_2_3_1_1_244
  35 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 144 (accept_3_4 34
  47 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 144
  (Polychromatic418967fa.accept_10_3_7_4_1_584 33 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 47 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 47 144 (accept_3_4 31 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 47 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 30 47 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 47 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 144 (accept_3_4 28 47
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 27 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 47 144 (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 47 144 (accept_3_4 25 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 47 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 24 47 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 47 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 23
  47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 144 (accept_3_4 22 47
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 21 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 47 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 47 144 (accept_3_4 19 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 47 144 (Polychromatic418967fa.accept_13_5_8_1_1_2161 18 47 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 47 144
  (Polychromatic418967fa.accept_19_17_9_11_1_6057 17 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 47 144 (accept_3_4 16 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  47 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 47 144 (Polychromatic418967fa.accept_19_14_9_11_1_7555 14 47 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 47 144 (accept_3_4 13 47 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 47 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 47 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 47 144 (accept_3_4 10 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  47 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 47 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 47 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 47 144 (accept_3_4 7 47 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 47 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 6 47 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 47 144
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 5 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 47 144 (accept_3_4 4 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 47
  144 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 47 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 47 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 47 144 (accept_3_4 1 47 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 47 144))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 144 (allA_succ_of_accept 45
  46 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 46 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 46 144 2 22 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 46 144 (Polychromatic418967fa.accept_11_10_2_1_1_1036 43 46 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 46 144 2 21 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 46 144 (accept_3_5 41 46 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 46 144 2 20 23 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 46 144
  (Polychromatic418967fa.accept_17_5_12_8_1_6304 39 46 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 46 144 2 19 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 46 144 (Polychromatic418967fa.accept_13_11_7_1_1_1386 37 46 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 46 144 2 18 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 46 144 (accept_3_5 35 46 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 34 46 144 2 17 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 46 144 (Polychromatic418967fa.accept_21_12_4_18_1_4424 33 46
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 46 144 2 16 23 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 46 144
  (Polychromatic418967fa.accept_19_12_8_11_1_7554 31 46 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 46 144 2 15 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 46 144 (accept_3_5 29 46 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 46
  144 2 14 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  46 144 (Polychromatic418967fa.accept_17_10_12_8_1_2748 27 46 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 46 144 2 13 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 46 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 46 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 46 144 2 12 23 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 46 144 (accept_3_5 23 46 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 46 144 2 11 23 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 46 144
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 46 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 46 144 2 10 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 46 144 (Polychromatic418967fa.accept_13_6_7_1_1_335 19 46 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 46 144 2 9 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 46 144 (accept_3_5 17 46 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 46 144 2 8 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 46 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 46 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 46 144 2 7 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 46 144 (Polychromatic418967fa.accept_21_13_4_18_1_7553
  13 46 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 46 144 2 6 23 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 46 144 (accept_3_5 11
  46 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 46 144 2 5 23 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 46 144
  (Polychromatic418967fa.accept_19_9_8_11_1_6072 9 46 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 46 144 2 4 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 46 144 (Polychromatic418967fa.accept_15_7_1_9_1_1500 7 46 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 46 144 2 3 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 46 144 (accept_3_5 5 46 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 46 144 2 2 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 46 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 46 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 46 144 2 1 23 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 46 144 (Polychromatic418967fa.accept_19_1_8_11_1_3378 1
  46 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 46
  144)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 45 144 (allA_succ_of_accept 44 45 144
  (Polychromatic418967fa.accept_13_5_6_1_1_822 44 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 45 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 43 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 45 144 3 14 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 45 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 41
  45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 144
  (Polychromatic418967fa.accept_21_19_3_18_1_7510 40 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 45 144 3 13 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 45 144 (Polychromatic418967fa.accept_21_17_3_18_1_7549 38 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 144 (Polychromatic418967fa.accept_19_18_7_11_1_7552 37 45
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 45 144 9 4 5 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 45 144
  (Polychromatic418967fa.accept_13_9_6_1_1_2902 35 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 34 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 45 144 3 11 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 45 144 (Polychromatic418967fa.accept_19_13_7_11_1_7551
  32 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 144
  (Polychromatic418967fa.accept_10_1_5_4_1_276 31 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 45 144 3 10 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 45 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 29 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 28 45 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 45 144 9 3 5 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 45 144
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 144 (Polychromatic418967fa.accept_21_4_3_18_1_7550 25 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 45 144 3 8 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 45 144 (Polychromatic418967fa.accept_19_4_7_11_1_6056 23 45 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 22 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 45 144 3 7 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 45 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 20 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 45 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 45 144 9 2 5 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 45 144
  (Polychromatic418967fa.accept_21_17_3_18_1_7549 17 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 45 144 3 5 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 45 144 (Polychromatic418967fa.accept_17_14_11_8_1_3854 14 45
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 13 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 45 144 3 4 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 45 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 144 (Polychromatic418967fa.accept_20_10_5_4_1_7511 10 45
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 45 144 9 1 5 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 45 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 144 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 45 144 3 2 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 45 144 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 45 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 144
  (Polychromatic418967fa.accept_19_4_7_11_1_6056 4 45 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 45 144 3 1 15 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 45 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 45 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 45 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  144))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 144 (allA_succ_of_accept 43 44 144 (accept_3_4 43 44
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 144 2 21 22 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 41 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 144 4 10 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 144 (Polychromatic418967fa.accept_19_1_6_11_1_7548 39 44 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 144 2 19 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 144 (accept_3_4 37 44 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 144 4 9 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 44 144 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 44 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 144 2 17 22 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 33 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 144 4 8 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 144 (accept_3_4 31 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  144 2 15 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 144 4 7 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 44 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 144 2 13 22 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 144 (accept_3_4 25 44 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 144 4 6 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 144 (Polychromatic418967fa.accept_14_9_2_4_1_1814 23 44 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 144 2 11 22 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 144
  (Polychromatic418967fa.accept_13_8_5_1_1_1381 21 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 144 4 5 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 144 (accept_3_4 19 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  144 2 9 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 144 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 144 4 4 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 144 (Polychromatic418967fa.accept_17_15_10_8_1_1708 15 44 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 144 2 7 22 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 144 (accept_3_4 13 44 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 144 4 3 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 44 144 (Polychromatic418967fa.accept_28_11_16_4_1_7547 11 44
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 144 2 5 22 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 144
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 144 4 2 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 144 (accept_3_4 7 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 144
  2 3 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  144 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 44 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 144 4 1 11 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 44 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 144 2 1 22 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 144 (accept_3_4 1 44 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 144)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 144 (allA_succ_of_accept 42 43
  144 (Polychromatic418967fa.accept_11_9_10_1_1_581 42 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 43 144 (accept_3_5 41 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 43 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 40 43 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 43 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 43 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 43 144 (accept_3_5 38 43 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 43 144 (Polychromatic418967fa.accept_10_7_3_4_1_978
  37 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 43 144
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 43 144 (accept_3_5 35 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34
  43 144 (Polychromatic418967fa.accept_15_4_13_9_1_3197 34 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 43 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 33 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 43 144 (accept_3_5 32 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 43 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 31 43 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 43 144
  (Polychromatic418967fa.accept_21_9_1_18_1_1761 30 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 43 144 (accept_3_5 29 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  43 144 (Polychromatic418967fa.accept_17_11_9_8_1_5038 28 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 43 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 43 144 (accept_3_5 26 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 43 144 (Polychromatic418967fa.accept_14_11_1_4_1_4445 25 43 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 43 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 24 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 43 144 (accept_3_5 23 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  43 144 (Polychromatic418967fa.accept_15_7_13_9_1_1466 22 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 43 144 (Polychromatic418967fa.accept_20_1_3_4_1_3213 21 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 43 144 (accept_3_5 20 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 43 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 43 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 43 144
  (Polychromatic418967fa.accept_13_5_4_1_1_364 18 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 43 144 (accept_3_5 17 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  43 144 (Polychromatic418967fa.accept_13_3_4_1_1_363 16 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 43 144 (Polychromatic418967fa.accept_19_15_5_11_1_4719 15 43 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 43 144 (accept_3_5 14 43 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 43 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 43
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 43 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 12 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 43 144 (accept_3_5 11 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  43 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 43 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 43 144 (accept_3_5 8 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 43 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 43 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 43 144
  (Polychromatic418967fa.accept_17_6_9_8_1_6316 6 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 43 144 (accept_3_5 5 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 43
  144 (Polychromatic418967fa.accept_15_4_13_9_1_3197 4 43 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 43 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 43 144 (accept_3_5 2 43 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 43 144 (Polychromatic418967fa.accept_17_1_9_8_1_7492 1 43 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 43 144)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 42 144 (allA_succ_of_accept 41 42 144 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 42 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 144 2 20 21 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 42 144 3 13 14 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 42 144 2 19 21 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 144
  (Polychromatic418967fa.accept_10_7_2_4_1_569 37 42 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 42 144 6 6 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 42 144 (Polychromatic418967fa.accept_15_5_12_9_1_2253 35 42 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 144 2 17 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 42 144 3 11 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 42 144 2 16 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 144 (Polychromatic418967fa.accept_13_5_3_1_1_1398
  31 42 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 144 6 5 7 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 144
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 29 42 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 42 144 2 14 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 27 42 144 3 9 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 42 144 2 13 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 42 144 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 42 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 144 6 4 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 144 (Polychromatic418967fa.accept_22_1_20_12_1_2869 23 42
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 42 144 2 11 21 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 42 144 3 7 14 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 42 144 2 10 21 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 144
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 42 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 42 144 6 3 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 42 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 42 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 144 2 8 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 42 144 3 5 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 42 144 2 7 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 42 144 (Polychromatic418967fa.accept_23_13_19_6_1_7546 13 42
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42 144 6 2 7 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 42 144
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 42 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 42 144 2 5 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 42 144 3 3 14 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 42 144 2 4 21 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 42 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 42 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 144 6 1 7 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 42 144 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 42 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 144 2 2 21 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 42 144 3 1 14 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 42 144 2 1 21 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 42 144
  (Polychromatic418967fa.accept_22_1_20_12_1_2869 1 42 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 42 144)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 144 (allA_succ_of_accept 40 41 144
  (accept_3_4 40 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 144
  (Polychromatic418967fa.accept_19_1_3_11_1_7545 39 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 41 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 38 41 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 41 144 (accept_3_4 37 41 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 41 144 (Polychromatic418967fa.accept_15_6_11_9_1_3215 36 41 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 41 144
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 41 144 (accept_3_4 34 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  41 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 33 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 41 144 (Polychromatic418967fa.accept_13_6_2_1_1_2137 32 41 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 41 144 (accept_3_4 31 41 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 41 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 30 41 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 41 144
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 41 144 (accept_3_4 28 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  41 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 41 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 41 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 41 144 (accept_3_4 25 41 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 41 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 24 41 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 41 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 41 144 (accept_3_4 22 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  41 144 (Polychromatic418967fa.accept_15_6_11_9_1_3215 21 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 41 144 (Polychromatic418967fa.accept_15_5_11_9_1_4276 20 41 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 41 144 (accept_3_4 19 41 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 41 144 (Polychromatic418967fa.accept_17_1_7_8_1_6347 18 41 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 41 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 17 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 41 144 (accept_3_4 16 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  41 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 41 144 (Polychromatic418967fa.accept_17_14_7_8_1_7544 14 41 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 41 144 (accept_3_4 13 41 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 41 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 41 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 41 144
  (Polychromatic418967fa.accept_20_11_1_4_1_7543 11 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 41 144 (accept_3_4 10 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  41 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 41 144 (Polychromatic418967fa.accept_19_8_3_11_1_6048 8 41 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 41 144 (accept_3_4 7 41 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 41 144 (Polychromatic418967fa.accept_13_6_2_1_1_2137 6 41 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 41 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 41 144 (accept_3_4 4 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 41
  144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 41 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 41 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 41 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 144 (accept_3_4 1 41 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 41 144))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 144 (allA_succ_of_accept 39 40 144
  (Polychromatic418967fa.accept_11_6_7_1_1_564 39 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 40 144 2 19 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 40 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 37 40 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 40 144 4 9 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 40 144 (accept_3_5 35 40 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 40 144 2 17 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 40 144 (Polychromatic418967fa.accept_15_3_10_9_1_769 33 40 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 40 144 8 4 5 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 40 144
  (Polychromatic418967fa.accept_15_1_10_9_1_1495 31 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 40 144 2 15 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 40 144 (accept_3_5 29 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 40
  144 4 7 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27
  40 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 27 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 40 144 2 13 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 40 144 (Polychromatic418967fa.accept_21_4_19_18_1_7542 25 40 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 40 144 8 3 5 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 40 144 (accept_3_5 23 40 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 40 144 2 11 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 40 144 (Polychromatic418967fa.accept_23_21_17_6_1_7541
  21 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 40 144 4 5 10 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 40 144
  (Polychromatic418967fa.accept_15_4_10_9_1_4298 19 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 40 144 2 9 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 40 144 (accept_3_5 17 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 40
  144 8 2 5 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  40 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 40 144 2 7 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 40 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 40 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 40 144 4 3 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 40 144 (accept_3_5 11 40 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 40 144 2 5 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 40 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 40 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 40 144 8 1 5 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 40 144
  (Polychromatic418967fa.accept_21_7_19_18_1_7540 7 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 40 144 2 3 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 40 144 (accept_3_5 5 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 40 144
  4 1 10 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 40
  144 (Polychromatic418967fa.accept_15_3_10_9_1_769 3 40 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 40 144 2 1 20 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 40 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 40 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 40 144)))))))))))))))))))))))))))))))))))))))) (allB_succ 39 144
  (allA_succ_of_accept 38 39 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 39 144 (Polychromatic418967fa.accept_17_3_5_8_1_1687 37 39 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 39 144 3 12 13 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 39 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 39 144 (Polychromatic418967fa.accept_19_15_1_11_1_7503 34 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 39 144 3 11 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 39 144 (Polychromatic418967fa.accept_23_9_16_6_1_7539
  32 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 39 144
  (Polychromatic418967fa.accept_19_12_1_11_1_7538 31 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 39 144 3 10 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 39 144 (Polychromatic418967fa.accept_11_7_6_1_1_2182 29 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 39 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 39 144 3 9 13 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 39 144
  (Polychromatic418967fa.accept_27_26_12_9_1_7537 26 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 25 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 39 144 3 8 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 39 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 39 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 144
  (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 39 144 3 7 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 39 144 (Polychromatic418967fa.accept_17_3_5_8_1_1687 20 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 39 144 (Polychromatic418967fa.accept_27_19_12_9_1_7536 19 39
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 39 144 3 6 13 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 39 144
  (Polychromatic418967fa.accept_23_17_16_6_1_7535 17 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 39 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 16 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 39 144 3 5 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 39 144 (Polychromatic418967fa.accept_20_14_19_4_1_7534 14 39
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 39 144
  (Polychromatic418967fa.accept_10_3_9_4_1_960 13 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 39 144 3 4 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 39 144 (Polychromatic418967fa.accept_23_11_16_6_1_7533 11 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 144 (Polychromatic418967fa.accept_19_10_1_11_1_7532 10 39
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 39 144 3 3 13 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 39 144
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 144 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 39 144 3 2 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 39 144 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 39 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 144
  (Polychromatic418967fa.accept_25_4_14_19_1_7531 4 39 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 39 144 3 1 13 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 39 144 (Polychromatic418967fa.accept_20_2_19_4_1_3246 2 39 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 144 (Polychromatic418967fa.accept_14_1_11_4_1_3430 1 39 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 144)))))))))))))))))))))))))))))))))))))))
  (allB_succ 38 144 (allA_succ_of_accept 37 38 144 (accept_3_4 37 38 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 38 144 2 18 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 38 144 (Polychromatic418967fa.accept_14_7_10_4_1_130 35 38 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 38 144 2 17 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 38 144 (Polychromatic418967fa.accept_15_3_8_9_1_795 33
  38 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 144 2 16 19 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 144 (accept_3_4 31
  38 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 144 2 15 19 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 29 38 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 144 2 14 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 38 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 144 2 13 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 144 (accept_3_4 25 38 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 144 2 12 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 144 (Polychromatic418967fa.accept_22_1_16_12_1_7499 23 38
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 144 2 11 19 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 144
  (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 38 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 144 2 10 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 144 (accept_3_4 19 38 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  144 2 9 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 144 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 38 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 144 2 8 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 38 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 144 2 7 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 144 (accept_3_4 13 38 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 144 2 6 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 144 (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 38 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 144 2 5 19 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 144
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 38 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 144 2 4 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 144 (accept_3_4 7 38 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 144
  2 3 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  144 (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 38 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 38 144 2 2 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 38 144 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 38 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 144 2 1 19 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 144 (accept_3_4 1 38 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 38 144)))))))))))))))))))))))))))))))))))))) (allB_succ 37 144 (allA_succ_of_accept 36
  37 144 (Polychromatic418967fa.accept_13_10_11_1_1_2152 36 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 37 144 (accept_3_5 35 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 37 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 34 37 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 37 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 33 37 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 37 144 (accept_3_5 32 37 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 37 144 (Polychromatic418967fa.accept_10_1_7_4_1_968
  31 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 37 144
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 37 144 (accept_3_5 29 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  37 144 (Polychromatic418967fa.accept_15_13_7_9_1_3210 28 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 37 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 27 37 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 37 144 (accept_3_5 26 37 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 37 144 (Polychromatic418967fa.accept_13_12_11_1_1_2920 25 37 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 37 144
  (Polychromatic418967fa.accept_21_3_16_18_1_7500 24 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 37 144 (accept_3_5 23 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  37 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 37 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 37 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 37 144 (accept_3_5 20 37 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 37 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 37 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 37 144
  (Polychromatic418967fa.accept_22_18_15_12_1_7530 18 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 37 144 (accept_3_5 17 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 37 144 (Polychromatic418967fa.accept_13_3_11_1_1_2122 16 37 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 37 144 (Polychromatic418967fa.accept_21_15_16_18_1_7529 15 37
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 37 144 (accept_3_5 14 37 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 37 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13
  37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 37 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 12 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 37 144 (accept_3_5 11 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  37 144 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 37 144 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 37 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 37 144 (accept_3_5 8 37 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 37 144 (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 37 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 37 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 6 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 37 144 (accept_3_5 5 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 37
  144 (Polychromatic418967fa.accept_19_4_18_11_1_7528 4 37 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 37 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 37 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 37 144 (accept_3_5 2 37 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 37 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 37 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 37 144))))))))))))))))))))))))))))))))))))) (allB_succ
  36 144 (allA_succ_of_accept 35 36 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 36 144 2 17 18 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 36 144 3 11 12 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 36 144 4 8 9 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 144
  (Polychromatic418967fa.accept_7_3_1_4_1_121 31 36 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 36 144 6 5 6 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 36 144 (Polychromatic418967fa.accept_15_14_6_9_1_2274 29 36 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 144 4 7 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 36 144 9 3 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 36 144 2 13 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 36 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 36 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36 144 12 2 3 12 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 36 144
  (Polychromatic418967fa.accept_19_4_17_11_1_7527 23 36 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 36 144 2 11 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 36 144 3 7 12 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 36 144 4 5 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 36 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 36 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 144 18 1 2 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 17 36 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 144 4 4 9 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 36 144 3 5 12 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 36 144 2 7 18 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 36 144
  (Polychromatic418967fa.accept_11_2_3_1_1_244 13 36 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 36 144 12 1 3 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 36 144 (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 36 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 36 144 2 5 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 36 144 9 1 4 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 36 144 4 2 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 144 (Polychromatic418967fa.accept_21_7_15_18_1_7526 7 36 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 144 6 1 6 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 36 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 36 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 36 144 4 1 9 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 36 144 3 1 12 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 36 144 2 1 18 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 1 36 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 36 144)))))))))))))))))))))))))))))))))))) (allB_succ 35 144
  (allA_succ_of_accept 34 35 144 (accept_3_4 34 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  35 144 (Polychromatic418967fa.accept_15_3_5_9_1_764 33 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 35 144 (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 35 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 35 144 (accept_3_4 31 35 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 35 144 (Polychromatic418967fa.accept_20_10_15_4_1_7525 30 35
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 35 144
  (Polychromatic418967fa.accept_10_9_5_4_1_966 29 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 35 144 (accept_3_4 28 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  35 144 (Polychromatic418967fa.accept_15_12_5_9_1_3234 27 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 35 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 35 144 (accept_3_4 25 35 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 35 144 (Polychromatic418967fa.accept_13_11_9_1_1_1407 24 35 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 35 144
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 35 144 (accept_3_4 22 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  35 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 35 144 (Polychromatic418967fa.accept_21_20_14_18_1_7524 20 35 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 35 144 (accept_3_4 19 35 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 35 144 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 35 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 35 144
  (Polychromatic418967fa.accept_14_3_7_4_1_118 17 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 35 144 (accept_3_4 16 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  35 144 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 35 144 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 35 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 35 144 (accept_3_4 13 35 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 35 144 (Polychromatic418967fa.accept_15_12_5_9_1_3234 12 35 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 35 144
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 35 144 (accept_3_4 10 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  35 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 35 144 (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 35 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 35 144 (accept_3_4 7 35 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 35 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 35 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 35 144
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 35 144 (accept_3_4 4 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 35
  144 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 35 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 35 144 (Polychromatic418967fa.accept_13_2_9_1_1_67 2 35 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 144 (accept_3_4 1 35 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 35 144))))))))))))))))))))))))))))))))))) (allB_succ 34 144 (allA_succ_of_accept 33 34 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 33 34 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 34 144 2 16 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 34 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 31 34 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 34 144 2 15 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 34 144 (accept_3_5 29 34 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 34 144 2 14 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 34 144 (Polychromatic418967fa.accept_15_12_4_9_1_3204 27 34 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 34 144 2 13 17 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 34 144
  (Polychromatic418967fa.accept_13_12_8_1_1_825 25 34 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 34 144 2 12 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 34 144 (accept_3_5 23 34 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 34
  144 2 11 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21
  34 144 (Polychromatic418967fa.accept_15_6_4_9_1_1438 21 34 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 34 144 2 10 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 34 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 19 34 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 34 144 2 9 17 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 34 144 (accept_3_5 17 34 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 34 144 2 8 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 34 144 (Polychromatic418967fa.accept_21_15_13_18_1_7523 15 34
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 34 144 2 7 17 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 34 144
  (Polychromatic418967fa.accept_15_13_4_9_1_2283 13 34 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 34 144 2 6 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 34 144 (accept_3_5 11 34 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 34
  144 2 5 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9
  34 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 34 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 34 144 2 4 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 34 144 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 34 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 34 144 2 3 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 34 144 (accept_3_5 5 34 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 34 144 2 2 17 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 34 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 34 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 34 144 2 1 17 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 34 144
  (Polychromatic418967fa.accept_19_1_15_11_1_4712 1 34 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 34 144)))))))))))))))))))))))))))))))))) (allB_succ 33 144 (allA_succ_of_accept 32 33 144
  (Polychromatic418967fa.accept_13_6_7_1_1_335 32 33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 144 (Polychromatic418967fa.accept_17_14_16_8_1_3861 31 33 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 33 144 3 10 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 33 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 29
  33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 144
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 28 33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 33 144 3 9 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 33 144 (Polychromatic418967fa.accept_17_9_16_8_1_2721 26 33 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 33 144 (Polychromatic418967fa.accept_15_10_3_9_1_3285 25 33
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 33 144 3 8 11 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 33 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 33 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 22 33 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 33 144 3 7 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 33 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 20 33 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 33 144
  (Polychromatic418967fa.accept_10_9_3_4_1_985 19 33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 33 144 3 6 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 33 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 33 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 33 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 33 144 3 5 11 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 33 144
  (Polychromatic418967fa.accept_17_14_16_8_1_3861 14 33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 33 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 33 144 3 4 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 33 144 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 33 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 144
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 10 33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 33 144 3 3 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 33 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 8 33 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 33 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 7 33 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 33 144 3 2 11 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 33 144
  (Polychromatic418967fa.accept_15_5_3_9_1_283 5 33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 33 144 (Polychromatic418967fa.accept_21_4_12_18_1_7522 4 33 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 33 144 3 1 11 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 33 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 33 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 1 33 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 33 144))))))))))))))))))))))))))))))))) (allB_succ 32 144 (allA_succ_of_accept 31 32 144 (accept_3_4 31 32
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32 144 2 15 16 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 32 144
  (Polychromatic418967fa.accept_13_3_6_1_1_3797 29 32 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 32 144 4 7 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 32 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 32 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 144 2 13 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 144 (accept_3_4 25 32 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 144 8 3 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 32 144 (Polychromatic418967fa.accept_15_8_2_9_1_3200 23 32 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 144 2 11 16 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 144
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 32 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 144 4 5 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 144 (accept_3_4 19 32 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  144 2 9 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 32 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 144 16 1 2 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 144 (Polychromatic418967fa.accept_13_2_6_1_1_3807 15 32 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 144 2 7 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 144 (accept_3_4 13 32 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 144 4 3 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 144 (Polychromatic418967fa.accept_15_11_2_9_1_1480 11 32 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 144 2 5 16 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 144
  (Polychromatic418967fa.accept_11_9_10_1_1_581 9 32 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 144 8 1 4 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 144 (accept_3_4 7 32 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 144
  2 3 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  144 (Polychromatic418967fa.accept_13_5_6_1_1_822 5 32 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 32 144 4 1 8 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 32 144 (Polychromatic418967fa.accept_13_3_6_1_1_3797 3 32 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 144 2 1 16 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 144 (accept_3_4 1 32 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 32 144)))))))))))))))))))))))))))))))) (allB_succ 31 144 (allA_succ_of_accept 30 31 144
  (Polychromatic418967fa.accept_13_4_5_1_1_833 30 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 31 144 (accept_3_5 29 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28
  31 144 (Polychromatic418967fa.accept_17_11_14_8_1_2729 28 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 31 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 27 31 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 31 144 (accept_3_5 26 31 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 31 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 25 31 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 31 144
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 24 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 31 144 (accept_3_5 23 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  31 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 22 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 31 144 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 31 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 31 144 (accept_3_5 20 31 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 31 144 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 31 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 31 144
  (Polychromatic418967fa.accept_19_18_12_11_1_3386 18 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 31 144 (accept_3_5 17 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 31 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 31 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 31 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 31 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 31 144 (accept_3_5 14 31 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 31 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 13
  31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 31 144
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 31 144 (accept_3_5 11 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  31 144 (Polychromatic418967fa.accept_11_10_9_1_1_2186 10 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 31 144 (Polychromatic418967fa.accept_13_9_5_1_1_1382 9 31 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 31 144 (accept_3_5 8 31 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 31 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 31 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 31 144
  (Polychromatic418967fa.accept_7_6_3_4_1_294 6 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 31 144 (accept_3_5 5 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 31
  144 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 31 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 31 144 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 31 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 31 144 (accept_3_5 2 31 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 31 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 31 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 31 144))))))))))))))))))))))))))))))) (allB_succ 30 144
  (allA_succ_of_accept 29 30 144 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 30 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 144 2 14 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 30 144 3 9 10 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 30 144 2 13 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 144 (Polychromatic418967fa.accept_20_5_10_4_1_4548
  25 30 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 144 6 4 5 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 144
  (Polychromatic418967fa.accept_13_10_4_1_1_2142 23 30 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 30 144 2 11 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 21 30 144 3 7 10 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 30 144 2 10 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 19 30 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 144 6 3 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 144 (Polychromatic418967fa.accept_21_17_9_18_1_7521 17 30
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 144 2 8 15 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 30 144 3 5 10 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 30 144 2 7 15 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 144
  (Polychromatic418967fa.accept_7_6_2_4_1_291 13 30 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 30 144 6 2 5 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 30 144 (Polychromatic418967fa.accept_20_11_10_4_1_7520 11 30 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 144 2 5 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 30 144 3 3 10 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 30 144 2 4 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 144 (Polychromatic418967fa.accept_21_7_9_18_1_7519 7 30 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 144 6 1 5 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 30 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 144 2 2 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 30 144 3 1 10 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 30 144 2 1 15 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 144 (Polychromatic418967fa.accept_20_1_10_4_1_7518 1 30 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 30 144)))))))))))))))))))))))))))))) (allB_succ 29 144 (allA_succ_of_accept
  28 29 144 (accept_3_4 28 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 144
  (Polychromatic418967fa.accept_15_12_14_9_1_778 27 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 26 29 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 144 (accept_3_4 25 29 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 24 29 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 144 (Polychromatic418967fa.accept_10_3_9_4_1_960
  23 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 144 (accept_3_4 22
  29 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 144
  (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 29 144 (Polychromatic418967fa.accept_13_7_3_1_1_814 20 29 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 144 (accept_3_4 19 29 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 29 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 29 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 17
  29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 144 (accept_3_4 16 29
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 144
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 29 144 (Polychromatic418967fa.accept_20_14_9_4_1_7517 14 29 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 144 (accept_3_4 13 29 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 29 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 12 29 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 144 (Polychromatic418967fa.accept_13_11_3_1_1_1397
  11 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 144 (accept_3_4 10
  29 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 144
  (Polychromatic418967fa.accept_21_9_8_18_1_7516 9 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 29 144 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 29 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 144 (accept_3_4 7 29 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 29 144 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 29 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 5
  29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 144 (accept_3_4 4 29 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3
  29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 144
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 144 (accept_3_4 1 29 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  144))))))))))))))))))))))))))))) (allB_succ 28 144 (allA_succ_of_accept 27 28 144
  (Polychromatic418967fa.accept_11_5_6_1_1_988 27 28 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 28 144 2 13 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 28 144 (Polychromatic418967fa.accept_13_12_2_1_1_2909 25 28 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 28 144 4 6 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 28 144 (accept_3_5 23 28 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 28 144 2 11 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 28 144 (Polychromatic418967fa.accept_19_2_9_11_1_7515 21 28 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 28 144 4 5 7 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 28 144
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 28 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 28 144 2 9 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 28 144 (accept_3_5 17 28 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 28
  144 4 4 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15
  28 144 (Polychromatic418967fa.accept_19_15_9_11_1_7514 15 28 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 28 144 2 7 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 28 144 (Polychromatic418967fa.accept_21_13_7_18_1_5966 13 28 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 28 144 4 3 7 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 28 144 (accept_3_5 11 28 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 28 144 2 5 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 28 144 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 28 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 28 144 4 2 7 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 28 144
  (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 28 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 28 144 2 3 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 28 144 (accept_3_5 5 28 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 28 144
  4 1 7 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 28 144
  (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 28 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 28 144 2 1 14 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 28 144 (Polychromatic418967fa.accept_17_1_11_8_1_2725 1 28 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 28 144)))))))))))))))))))))))))))) (allB_succ 27 144 (allA_succ_of_accept 26
  27 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 26 27 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 27 144 (Polychromatic418967fa.accept_15_10_12_9_1_776 25 27 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 27 144 3 8 9 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 27 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 23 27 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 22 27 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 27 144 3 7 9 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 27 144 (Polychromatic418967fa.accept_15_5_12_9_1_2253 20 27 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 19 27 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 27 144 9 2 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 27 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 27 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 16 27 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 27 144 3 5 9 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 27 144
  (Polychromatic418967fa.accept_15_14_12_9_1_3216 14 27 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 27 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 27 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 27 144 3 4 9 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 27 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 27 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 144
  (Polychromatic418967fa.accept_7_3_6_4_1_30 10 27 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 27 144 9 1 3 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 27 144 (Polychromatic418967fa.accept_25_8_2_19_1_7513 8 27 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 144 (Polychromatic418967fa.accept_19_7_8_11_1_3379 7 27 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 27 144 3 2 9 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 27 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 27 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 27 144 (Polychromatic418967fa.accept_15_4_12_9_1_773 4 27 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 27 144 3 1 9 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 27 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 2 27 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 27 144
  (Polychromatic418967fa.accept_10_1_7_4_1_968 1 27 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 27 144))))))))))))))))))))))))))) (allB_succ 26 144 (allA_succ_of_accept 25 26 144 (accept_3_4 25 26 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 144 2 12 13 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 144
  (Polychromatic418967fa.accept_7_2_5_4_1_115 23 26 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 26 144 2 11 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 26 144 (Polychromatic418967fa.accept_15_6_11_9_1_3215 21 26 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 26 144 2 10 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 26 144 (accept_3_4 19 26 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26 144 2 9 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 26 144 (Polychromatic418967fa.accept_15_2_11_9_1_263 17 26 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 26 144 2 8 13 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 26 144
  (Polychromatic418967fa.accept_7_1_5_4_1_134 15 26 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 26 144 2 7 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 26 144 (accept_3_4 13 26 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26
  144 2 6 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  26 144 (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 26 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 26 144 2 5 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 26 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 26 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 26 144 2 4 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 26 144 (accept_3_4 7 26 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 144 2 3 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 26 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 26 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 26 144 2 2 13 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 26 144
  (Polychromatic418967fa.accept_21_3_5_18_1_7512 3 26 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 26 144 2 1 13 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 26 144 (accept_3_4 1 26 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 26
  144)))))))))))))))))))))))))) (allB_succ 25 144 (allA_succ_of_accept 24 25 144
  (Polychromatic418967fa.accept_11_2_3_1_1_244 24 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 25 144 (accept_3_5 23 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22
  25 144 (Polychromatic418967fa.accept_14_8_11_4_1_3438 22 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 25 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 25 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 25 144 (accept_3_5 20 25 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 25 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 19 25 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 25 144
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 18 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 25 144 (accept_3_5 17 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  25 144 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 25 144 (Polychromatic418967fa.accept_13_2_12_1_1_343 15 25 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 25 144 (accept_3_5 14 25 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 25 144 (Polychromatic418967fa.accept_11_2_3_1_1_244 13 25 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 25 144
  (Polychromatic418967fa.accept_15_12_10_9_1_798 12 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 25 144 (accept_3_5 11 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  25 144 (Polychromatic418967fa.accept_20_10_5_4_1_7511 10 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 25 144 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 25 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 25 144 (accept_3_5 8 25 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 25 144 (Polychromatic418967fa.accept_14_7_11_4_1_3455 7 25 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 25 144
  (Polychromatic418967fa.accept_10_6_5_4_1_571 6 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 25 144 (accept_3_5 5 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 25
  144 (Polychromatic418967fa.accept_15_4_10_9_1_4298 4 25 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 25 144 (Polychromatic418967fa.accept_15_3_10_9_1_769 3 25 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 25 144 (accept_3_5 2 25 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 25 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 25 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 25 144))))))))))))))))))))))))) (allB_succ 24 144
  (allA_succ_of_accept 23 24 144 (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 24 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 144 2 11 12 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 24 144 3 7 8 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 24 144 4 5 6 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 24 144 (Polychromatic418967fa.accept_21_19_3_18_1_7510
  19 24 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24 144 6 3 4 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 24 144
  (Polychromatic418967fa.accept_19_17_5_11_1_7509 17 24 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 24 144 8 2 3 18 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 24 144 3 5 8 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 24 144 2 7 12 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 24 144 (Polychromatic418967fa.accept_7_6_3_4_1_294 13 24 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 144 12 1 2 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 24 144 (Polychromatic418967fa.accept_21_11_3_18_1_3068 11 24
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 144 2 5 12 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 24 144 3 3 8 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 24 144 8 1 3 18 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 24 144
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 24 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 24 144 6 1 4 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 24 144 (Polychromatic418967fa.accept_21_5_3_18_1_7508 5 24 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 24 144 4 1 6 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 24 144 3 1 8 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 24 144 2 1 12 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 24 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 24 144)))))))))))))))))))))))) (allB_succ 23
  144 (allA_succ_of_accept 22 23 144 (accept_3_4 22 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 23 144 (Polychromatic418967fa.accept_19_2_4_11_1_7507 21 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 23 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 20 23 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 144 (accept_3_4 19 23 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 23 144 (Polychromatic418967fa.accept_15_3_8_9_1_795 18 23 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 144
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 144 (accept_3_4 16 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 144 (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 144 (Polychromatic418967fa.accept_15_14_8_9_1_1452 14 23 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 144 (accept_3_4 13 23 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 12 23 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 144
  (Polychromatic418967fa.accept_13_11_10_1_1_1409 11 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 144 (accept_3_4 10 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 144 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 144 (Polychromatic418967fa.accept_22_8_1_12_1_7506 8 23 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 144 (accept_3_4 7 23 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 6 23 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 144
  (Polychromatic418967fa.accept_7_5_2_4_1_126 5 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 144 (accept_3_4 4 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  144 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 23 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 144 (Polychromatic418967fa.accept_14_2_9_4_1_1735 2 23 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 144 (accept_3_4 1 23 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 144))))))))))))))))))))))) (allB_succ 22 144 (allA_succ_of_accept 21 22 144
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 21 22 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 22 144 2 10 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 22 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 19 22 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 22 144 2 9 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 22 144 (accept_3_5 17 22 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 22 144 2 8 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 22 144 (Polychromatic418967fa.accept_13_2_9_1_1_67 15 22 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 22 144 2 7 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 22 144 (Polychromatic418967fa.accept_15_13_7_9_1_3210
  13 22 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 22 144 2 6 11 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 22 144 (accept_3_5 11
  22 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 22 144 2 5 11 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 22 144
  (Polychromatic418967fa.accept_19_9_3_11_1_7505 9 22 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 22 144 2 4 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 22 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 22 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 22 144 2 3 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 22 144 (accept_3_5 5 22 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 22 144 2 2 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 22 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 22 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 22 144 2 1 11 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 22 144 (Polychromatic418967fa.accept_15_1_7_9_1_20 1 22
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 22 144)))))))))))))))))))))) (allB_succ 21
  144 (allA_succ_of_accept 20 21 144 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 21 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 144 (Polychromatic418967fa.accept_13_6_8_1_1_2913
  19 21 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 21 144 3 6 7 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 21 144
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 21 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 21 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 16 21 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 21 144 3 5 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 21 144 (Polychromatic418967fa.accept_15_14_6_9_1_2274 14 21 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 144
  (Polychromatic418967fa.accept_11_2_10_1_1_1017 13 21 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 21 144 3 4 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 21 144 (Polychromatic418967fa.accept_13_11_8_1_1_3815 11 21 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 144 (Polychromatic418967fa.accept_14_10_7_4_1_3453 10 21
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 21 144 3 3 7 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 21 144
  (Polychromatic418967fa.accept_19_8_2_11_1_7504 8 21 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 144 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 21 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 21 144 3 2 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 21 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 21 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 144
  (Polychromatic418967fa.accept_15_4_6_9_1_2269 4 21 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 21 144 3 1 7 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 21 144 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 21 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 1 21 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 144))))))))))))))))))))) (allB_succ 20 144
  (allA_succ_of_accept 19 20 144 (accept_3_4 19 20 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20
  144 2 9 10 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  20 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 17 20 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 20 144 4 4 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 20 144 (Polychromatic418967fa.accept_19_15_1_11_1_7503 15 20 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 144 2 7 10 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 144 (accept_3_4 13 20 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 20 144 4 3 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 20 144 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 20 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 144 2 5 10 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 144
  (Polychromatic418967fa.accept_7_2_6_4_1_29 9 20 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 20 144 4 2 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 20 144 (accept_3_4 7 20 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 144
  2 3 10 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20
  144 (Polychromatic418967fa.accept_7_5_6_4_1_117 5 20 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 144 4 1 5 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 20 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 144 2 1 10 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 144 (accept_3_4 1 20 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 144)))))))))))))))))))) (allB_succ 19 144 (allA_succ_of_accept 18 19 144
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 19 144 (accept_3_5 17 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16
  19 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 16 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 19 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 15 19 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 19 144 (accept_3_5 14 19 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 19 144 (Polychromatic418967fa.accept_7_6_5_4_1_297 13 19 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 19 144
  (Polychromatic418967fa.accept_15_12_4_9_1_3204 12 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 19 144 (accept_3_5 11 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10
  19 144 (Polychromatic418967fa.accept_15_10_4_9_1_3203 10 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 19 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 9 19 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 19 144 (accept_3_5 8 19 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 19 144 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 19 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 19 144
  (Polychromatic418967fa.accept_7_6_5_4_1_297 6 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 19 144 (accept_3_5 5 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 19
  144 (Polychromatic418967fa.accept_11_4_8_1_1_1047 4 19 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 19 144 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 19 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 19 144 (accept_3_5 2 19 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 19 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 19 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 19 144))))))))))))))))))) (allB_succ 18 144
  (allA_succ_of_accept 17 18 144 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 18 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 144 2 8 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 18 144 3 5 6 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 18 144 2 7 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 18 144 (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 18 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18 144 6 2 3 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 18 144
  (Polychromatic418967fa.accept_17_11_1_8_1_7502 11 18 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 18 144 2 5 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 18 144 9 1 2 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 18 144 2 4 9 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 18 144 (Polychromatic418967fa.accept_17_7_1_8_1_6280 7 18 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 144 6 1 3 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 18 144 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 18 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 144 2 2 9 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 18 144 3 1 6 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 18 144 2 1 9 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 18 144
  (Polychromatic418967fa.accept_19_1_18_11_1_4704 1 18 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 18 144)))))))))))))))))) (allB_succ 17 144 (allA_succ_of_accept 16 17 144 (accept_3_4 16 17 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 15 17 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 144
  (Polychromatic418967fa.accept_19_14_17_11_1_7501 14 17 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 17 144 (accept_3_4 13 17 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 17 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 17 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 17 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 17 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 144 (accept_3_4 10 17 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 144 (Polychromatic418967fa.accept_19_9_17_11_1_2226
  9 17 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 144
  (Polychromatic418967fa.accept_7_1_3_4_1_128 8 17 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 144 (accept_3_4 7 17 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  144 (Polychromatic418967fa.accept_7_6_3_4_1_294 6 17 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 144 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 17 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 144 (accept_3_4 4 17 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 17 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 144 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  17 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 144 (accept_3_4 1 17 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 144))))))))))))))))) (allB_succ 16 144 (allA_succ_of_accept 15
  16 144 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 16 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 16 144 2 7 8 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 16 144 (Polychromatic418967fa.accept_7_6_2_4_1_291 13 16 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 16 144 4 3 4 36 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 16 144 (accept_3_5 11 16 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 16 144 2 5 8 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 16 144 (Polychromatic418967fa.accept_14_9_2_4_1_1814 9 16 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 16 144 8 1 2 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 16 144
  (Polychromatic418967fa.accept_13_7_3_1_1_814 7 16 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 16 144 2 3 8 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 16 144 (accept_3_5 5 16 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 16 144
  4 1 4 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 16 144
  (Polychromatic418967fa.accept_21_3_16_18_1_7500 3 16 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 16 144 2 1 8 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 16 144 (Polychromatic418967fa.accept_22_1_16_12_1_7499 1 16 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 16 144)))))))))))))))) (allB_succ 15 144 (allA_succ_of_accept 14 15 144
  (Polychromatic418967fa.accept_19_14_15_11_1_4739 14 15 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 15 144 (Polychromatic418967fa.accept_17_13_15_8_1_3860 13 15 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 15 144 3 4 5 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 15 144
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 15 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 15 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 10 15 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 15 144 3 3 5 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 15 144 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 15 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 15 144
  (Polychromatic418967fa.accept_19_7_15_11_1_3420 7 15 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 15 144 3 2 5 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 15 144 (Polychromatic418967fa.accept_7_5_1_4_1_122 5 15 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 144 (Polychromatic418967fa.accept_19_4_15_11_1_7498 4 15 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 15 144 3 1 5 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 15 144
  (Polychromatic418967fa.accept_19_2_15_11_1_7497 2 15 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 15 144 (Polychromatic418967fa.accept_10_1_5_4_1_276 1 15 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 15 144))))))))))))))) (allB_succ 14 144 (allA_succ_of_accept 13 14 144
  (accept_3_4 13 14 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 144 2 6 7 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 144
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 11 14 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 144 2 5 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 144 (Polychromatic418967fa.accept_19_9_14_11_1_7496 9 14 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 144 2 4 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 144 (accept_3_4 7 14 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 144 2 3 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 144 (Polychromatic418967fa.accept_15_5_14_9_1_274 5 14 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 144 2 2 7 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 144 (Polychromatic418967fa.accept_19_3_14_11_1_2214
  3 14 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 144 2 1 7 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 144 (accept_3_4 1 14
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 144)))))))))))))) (allB_succ 13 144 (allA_succ_of_accept 12
  13 144 (Polychromatic418967fa.accept_7_5_6_4_1_117 12 13 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 13 144 (accept_3_5 11 13 144 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 13 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 10 13 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 13 144 (Polychromatic418967fa.accept_7_2_6_4_1_29 9 13 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 13 144 (accept_3_5 8 13 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 13 144 (Polychromatic418967fa.accept_10_7_3_4_1_978 7
  13 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 13 144
  (Polychromatic418967fa.accept_19_6_13_11_1_7495 6 13 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 13 144 (accept_3_5 5 13 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 13
  144 (Polychromatic418967fa.accept_15_4_13_9_1_3197 4 13 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 13 144 (Polychromatic418967fa.accept_7_3_6_4_1_30 3 13 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 13 144 (accept_3_5 2 13 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 13 144 (Polychromatic418967fa.accept_22_1_13_12_1_7494 1 13 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 13 144))))))))))))) (allB_succ 12 144
  (allA_succ_of_accept 11 12 144 (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 12 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 12 144 2 5 6 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 12 144 3 3 4 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 12 144 4 2 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 144 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 12 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 144 6 1 2 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 12 144
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 5 12 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 12 144 4 1 3 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 12 144 3 1 4 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 12 144 2 1 6 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 144 (Polychromatic418967fa.accept_7_1_5_4_1_134 1 12 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 12 144)))))))))))) (allB_succ 11 144 (allA_succ_of_accept 10 11 144
  (accept_3_4 10 11 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 144
  (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 11 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 144 (Polychromatic418967fa.accept_13_8_11_1_1_3789 8 11 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 144 (accept_3_4 7 11 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 144 (Polychromatic418967fa.accept_15_6_11_9_1_3215 6 11 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 144 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5
  11 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 144 (accept_3_4 4 11 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 144 (Polychromatic418967fa.accept_13_3_11_1_1_2122
  3 11 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 144
  (Polychromatic418967fa.accept_15_2_11_9_1_263 2 11 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 144 (accept_3_4 1 11 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  144))))))))))) (allB_succ 10 144 (allA_succ_of_accept 9 10 144 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 10 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 10 144 2 4 5 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 10 144
  (Polychromatic418967fa.accept_14_7_10_4_1_130 7 10 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 10 144 2 3 5 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 10 144 (accept_3_5 5 10 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 10 144
  2 2 5 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 10 144
  (Polychromatic418967fa.accept_15_3_10_9_1_769 3 10 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 10 144 2 1 5 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 10 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 10 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 10 144)))))))))) (allB_succ 9 144 (allA_succ_of_accept 8 9 144
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 9 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 9 144 (Polychromatic418967fa.accept_19_7_9_11_1_7493 7 9 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 9 144 3 2 3 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 9 144 (Polychromatic418967fa.accept_7_5_2_4_1_126 5 9 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 144
  (Polychromatic418967fa.accept_21_4_9_18_1_6001 4 9 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 9 144 3 1 3 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 9 144 (Polychromatic418967fa.accept_13_2_9_1_1_67 2 9 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 144 (Polychromatic418967fa.accept_17_1_9_8_1_7492 1 9 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 144))))))))) (allB_succ 8 144
  (allA_succ_of_accept 7 8 144 (accept_3_4 7 8 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 144 2
  3 4 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 144
  (Polychromatic418967fa.accept_7_5_1_4_1_122 5 8 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 8 144 4 1 2 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 8 144 (Polychromatic418967fa.accept_7_3_1_4_1_121 3 8 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 144 2 1 4 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 144 (accept_3_4 1 8 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 8 144)))))))) (allB_succ 7 144 (allA_succ_of_accept 6 7 144
  (Polychromatic418967fa.accept_11_6_7_1_1_564 6 7 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 7 144 (accept_3_5 5 7 144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 7 144
  (Polychromatic418967fa.accept_17_4_7_8_1_7491 4 7 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 7 144 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 7 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 7 144 (accept_3_5 2 7 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 7 144 (Polychromatic418967fa.accept_10_1_7_4_1_968 1 7 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 7 144))))))) (allB_succ 6 144 (allA_succ_of_accept 5 6 144
  (Polychromatic418967fa.accept_7_5_6_4_1_117 5 6 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 144 2 2 3 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 6 144 3 1 2 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 6 144 2 1 3 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 144 (Polychromatic418967fa.accept_15_1_6_9_1_254 1 6 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 6 144)))))) (allB_succ 5 144 (allA_succ_of_accept 4 5 144 (accept_3_4 4 5
  144 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 144
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 5 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 5 144 (Polychromatic418967fa.accept_7_2_5_4_1_115 2 5 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 144 (accept_3_4 1 5 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 5 144))))) (allB_succ 4 144 (allA_succ_of_accept 3 4 144
  (Polychromatic418967fa.accept_13_3_4_1_1_363 3 4 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 4 144 2 1 2 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 4 144 (Polychromatic418967fa.accept_17_1_4_8_1_5049 1 4 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 4 144)))) (allB_succ 3 144 (allA_succ_of_accept 2 3 144
  (Polychromatic418967fa.accept_11_2_3_1_1_244 2 3 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 3 144 (Polychromatic418967fa.accept_7_1_3_4_1_128 1 3 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 144))) (allB_succ 2 144 (allA_succ_of_accept 1 2 144 (accept_3_4 1 2 144
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 144)) (allB_two
  144))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


