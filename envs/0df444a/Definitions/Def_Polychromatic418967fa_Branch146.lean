-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch146
-- name    : Polychromatic418967fa_Branch146
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:14:49.195241+00:00
-- url     : https://prove2.me/theorems/60464bbe-de5e-4985-9ac4-e9553f22047d
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

def Polychromatic418967fa.branch_146 : allB 146 146 :=
  allB_succ' 2 145 146 (Eq.refl Bool.true) (allA_of_3_0 2 145 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  144 146 (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 146 2 1 72 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 146 (accept_3_2 1 144 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 144 146))) (allB_succ' 4 143 146 (Eq.refl Bool.true) (allA_succ_of_accept 3 143 146
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 143 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 143 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 146 (accept_3_2 1 143 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 143 146)))) (allB_succ' 5 142 146 (Eq.refl Bool.true) (allA_of_3_0 5 142 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 141 146 (Eq.refl Bool.true) (allA_succ_of_accept 5 141 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 146 (accept_3_2 4 141 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 141 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 146 (accept_3_2 1 141 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 146)))))) (allB_succ' 7 140 146 (Eq.refl Bool.true) (allA_succ_of_gcd 6 140 146 2 3
  70 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 146
  (Polychromatic418967fa.accept_11_5_8_3_1_66 5 140 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 140 146 2 2 70 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 140 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 140 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 146 2 1 70 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 146 (accept_3_2 1 140 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 140 146))))))) (allB_succ' 8 139 146 (Eq.refl Bool.true) (allA_of_3_0 8 139 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 138 146 (Eq.refl Bool.true) (allA_succ_of_gcd 8 138 146 2 4 69 73
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 146
  (accept_3_2 7 138 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 146 2 3 69 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 138 146 2 2 69 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 138 146 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 138 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 146 2 1 69 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 146 (accept_3_2 1 138 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 138 146))))))))) (allB_succ' 10 137 146 (Eq.refl Bool.true) (allA_succ_of_accept 9 137 146
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 137 146 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 137 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 146 (accept_3_2 7 137 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 137 146 (Polychromatic418967fa.accept_15_6_2_11_1_325 6 137 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  137 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 146 (accept_3_2 4 137
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 146 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 137 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 137 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 146 (accept_3_2 1 137 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  146)))))))))) (allB_succ' 11 136 146 (Eq.refl Bool.true) (allA_of_3_0 11 136 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 135 146 (Eq.refl Bool.true) (allA_succ_of_accept 11 135 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 146 (accept_3_2 10 135 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 135 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 146 (accept_3_2 7 135 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 135 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 146 (accept_3_2 4 135 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 146 (Polychromatic418967fa.accept_13_2_5_3_1_406 2 135 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 146 (accept_3_2 1 135 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 135 146)))))))))))) (allB_succ' 13 134 146 (Eq.refl Bool.true) (allA_succ_of_gcd 12 134
  146 2 6 67 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  134 146 (Polychromatic418967fa.accept_16_11_6_2_1_4155 11 134 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 134 146 2 5 67 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 134 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 134 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 146 2 4 67 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 146 (accept_3_2 7 134 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134 146 2 3 67 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 134 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 134 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 146 2 2 67 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 146
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 134 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 134 146 2 1 67 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 134 146 (accept_3_2 1 134 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  146))))))))))))) (allB_succ' 14 133 146 (Eq.refl Bool.true) (allA_of_3_0 14 133 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 132 146 (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 146 2 7 66 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 146 (accept_3_2 13 132 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 146 2 6 66 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 146
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 132 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 146 2 5 66 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 132 146 (Polychromatic418967fa.accept_13_9_2_3_1_3027 9 132 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 132 146 2 4 66 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 132 146 (accept_3_2 7 132 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 132 146 2 3 66 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 132 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 146 2 2 66 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 132 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 3
  132 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 146 2 1 66 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 146 (accept_3_2 1
  132 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132 146))))))))))))))) (allB_succ' 16 131 146 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 131 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 146
  (Polychromatic418967fa.accept_20_14_11_6_1_6264 14 131 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 146 (accept_3_2 13 131 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 131 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 146 (accept_3_2 10 131 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  131 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 131 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 146 (accept_3_2 7 131 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 131 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 146 (accept_3_2 4 131 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 146
  (Polychromatic418967fa.accept_10_2_1_6_1_634 2 131 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 146 (accept_3_2 1 131 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  146)))))))))))))))) (allB_succ' 17 130 146 (Eq.refl Bool.true) (allA_of_3_0 17 130 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 18 129 146 (Eq.refl Bool.true) (allA_succ_of_accept 17 129 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 146 (accept_3_2 16 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 129 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 146 (accept_3_2 13 129 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 146 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 129 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 146 (accept_3_2 10 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 129 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 146 (accept_3_2 7 129 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 129 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 146 (accept_3_2 4 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 129 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 146 (accept_3_2 1 129 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129 146)))))))))))))))))) (allB_succ' 19 128 146 (Eq.refl Bool.true) (allA_succ_of_gcd
  18 128 146 2 9 64 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 128 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 146 2 8 64 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  128 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 146 2 7 64 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 146 (accept_3_2 13
  128 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 146 2 6 64 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 146
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 128 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 146 2 5 64 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 146 (Polychromatic418967fa.accept_21_9_2_20_1_857 9 128 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 146 2 4 64 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 146 (accept_3_2 7 128 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 146 2 3 64 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 146 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 128 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 146 2 2 64 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 3
  128 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 146 2 1 64 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 146 (accept_3_2 1
  128 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128 146))))))))))))))))))) (allB_succ' 20 127 146 (Eq.refl
  Bool.true) (allA_of_3_0 20 127 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 21 126 146 (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 126 146 2 10 63 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 146 (accept_3_2 19 126 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 146 2 9 63 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 146 (Polychromatic418967fa.accept_15_2_6_11_1_1587 17 126 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 146 2 8 63 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 146 (Polychromatic418967fa.accept_12_3_6_2_1_747
  15 126 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 146 2 7 63 73
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 146
  (accept_3_2 13 126 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 146 2 6 63 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 146
  (Polychromatic418967fa.accept_19_11_12_13_1_4844 11 126 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 126 146 2 5 63 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 126 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 126 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 146 2 4 63 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 146 (accept_3_2 7 126 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 146 2 3 63 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 146 (Polychromatic418967fa.accept_13_5_9_3_1_870 5 126 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 146 2 2 63 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 146
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 126 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 126 146 2 1 63 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 126 146 (accept_3_2 1 126 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  146))))))))))))))))))))) (allB_succ' 22 125 146 (Eq.refl Bool.true) (allA_succ_of_accept 21 125 146
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 125 146 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 125 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 146 (accept_3_2 19 125 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 125 146 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 125 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 146
  (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 146 (accept_3_2 16 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 125 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 146 (accept_3_2 13 125 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 146 (accept_3_2 10 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 146 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 125 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 146 (accept_3_2 7 125 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 125 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 5 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 146 (accept_3_2 4 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 146 (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 125 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 146 (accept_3_2 1 125 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 125 146)))))))))))))))))))))) (allB_succ' 23 124 146 (Eq.refl Bool.true)
  (allA_of_3_0 23 124 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 123 146 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 123 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 146 (accept_3_2 22 123 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 123 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 123 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 123 146
  (Polychromatic418967fa.accept_25_20_23_21_1_7825 20 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 123 146 (accept_3_2 19 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 123 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 123 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 123 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 146 (accept_3_2 16 123 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 123 146
  (Polychromatic418967fa.accept_17_15_4_10_1_3968 15 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 123 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 146 (accept_3_2 13 123 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 146 (accept_3_2 10 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 123 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 146 (accept_3_2 7 123 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 123 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 146 (accept_3_2 4 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 123 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 123 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 146 (accept_3_2 1 123 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 146)))))))))))))))))))))))) (allB_succ' 25 122 146 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 122 146 2 12 61 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 122 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 146 2 11 61 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 146
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 122 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 146 2 10 61 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 146 (accept_3_2 19 122 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 146 2 9 61 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 146 2 8 61 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  122 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 146 2 7 61 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 146 (accept_3_2 13
  122 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 146 2 6 61 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 146
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 122 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 146 2 5 61 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 122 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 146 2 4 61 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 146 (accept_3_2 7 122 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 146 2 3 61 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 146 (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 122 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 146 2 2 61 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  122 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 146 2 1 61 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 146 (accept_3_2 1
  122 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 146))))))))))))))))))))))))) (allB_succ' 26 121 146
  (Eq.refl Bool.true) (allA_of_3_0 26 121 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 120 146 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 120 146 2 13 60 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 120 146 (accept_3_2 25 120 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 146 2 12 60 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 120 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 120 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 146 2 11 60 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 146
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 120 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 146 2 10 60 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 120 146 (accept_3_2 19 120 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 146 2 9 60 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 120 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 146 2 8 60 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 120 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  120 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 146 2 7 60 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 146 (accept_3_2 13
  120 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 146 2 6 60 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 146
  (Polychromatic418967fa.accept_17_11_1_10_1_3925 11 120 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 120 146 2 5 60 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 120 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 120 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 146 2 4 60 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 146 (accept_3_2 7 120 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 146 2 3 60 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 120 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 120 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 146 2 2 60 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 146
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 3 120 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 120 146 2 1 60 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 120 146 (accept_3_2 1 120 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  146))))))))))))))))))))))))))) (allB_succ' 28 119 146 (Eq.refl Bool.true) (allA_succ_of_accept 27 119 146
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 119 146 (Polychromatic418967fa.accept_19_7_5_13_1_3493 26 119 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 119 146 (accept_3_2 25 119 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 119 146 (Polychromatic418967fa.accept_13_11_2_3_1_883 24 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 119 146
  (Polychromatic418967fa.accept_10_3_9_6_1_94 23 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 119 146 (accept_3_2 22 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 119 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 119 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 119 146 (accept_3_2 19 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 119 146 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 119
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 119 146 (accept_3_2 16 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 119 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 119 146 (Polychromatic418967fa.accept_13_1_2_3_1_911 14 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 119 146 (accept_3_2 13 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 119 146 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 119
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 119 146
  (Polychromatic418967fa.accept_13_11_2_3_1_883 11 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 119 146 (accept_3_2 10 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  119 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 119 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 119 146 (accept_3_2 7 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 119 146 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 119 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 119 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 119 146 (accept_3_2 4 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  119 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 119 146 (Polychromatic418967fa.accept_21_2_14_20_1_841 2 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 119 146 (accept_3_2 1 119 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 119 146)))))))))))))))))))))))))))) (allB_succ' 29 118 146 (Eq.refl
  Bool.true) (allA_of_3_0 29 118 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 30 117 146 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 117 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 146 (accept_3_2 28 117 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 117 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 117 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 117 146 (Polychromatic418967fa.accept_11_4_7_3_1_289
  26 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 146 (accept_3_2 25
  117 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 146
  (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 117 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 146 (accept_3_2 22 117 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 117 146 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 117 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 117 146
  (Polychromatic418967fa.accept_22_20_7_14_1_7824 20 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 117 146 (accept_3_2 19 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 117 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 117 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 146 (accept_3_2 16 117 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 117 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 117 146
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 117 146 (accept_3_2 13 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 117 146 (Polychromatic418967fa.accept_19_12_3_13_1_4911 12 117 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 146 (accept_3_2 10
  117 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 117 146
  (Polychromatic418967fa.accept_19_9_3_13_1_2300 9 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 117 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 117 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 146 (accept_3_2 7 117 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 117 146 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 117 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5
  117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 146 (accept_3_2 4 117
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 117 146 (Polychromatic418967fa.accept_4_3_1_2_1_62
  3 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 117 146
  (Polychromatic418967fa.accept_17_2_15_10_1_5171 2 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 146 (accept_3_2 1 117 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  146)))))))))))))))))))))))))))))) (allB_succ' 31 116 146 (Eq.refl Bool.true) (allA_succ_of_gcd 30 116 146 2 15 58 73
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 146
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 116 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 146 2 14 58 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 116 146 (Polychromatic418967fa.accept_19_8_2_13_1_2328 27 116 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 146 2 13 58 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 146 (accept_3_2 25 116 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 146 2 12 58 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 116 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 116 146 2 11 58 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 116 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 116 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 116 146 2 10 58 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 116 146 (accept_3_2 19 116 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 116 146 2 9 58 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 116 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  116 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 146 2 8 58 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 116 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 146 2 7 58 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 116 146 (accept_3_2 13 116 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  116 146 2 6 58 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 116 146 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 116 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 146 2 5 58 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 116 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 146 2 4 58 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 146 (accept_3_2 7 116 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 146 2 3 58 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 116 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 146 2 2 58 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 116 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 146 2 1 58 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 146 (accept_3_2 1 116 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  146))))))))))))))))))))))))))))))) (allB_succ' 32 115 146 (Eq.refl Bool.true) (allA_of_3_0 32 115 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 114 146 (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 146 2 16 57 73
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 146
  (accept_3_2 31 114 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 146 2 15 57 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 114 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 146 2 14 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 114 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 114 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 114 146 2 13 57 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 146 (accept_3_2 25 114 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 146 2 12 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  114 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 146 2 11 57 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 146
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 146 2 10 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 146 (accept_3_2 19 114 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 146 2 9 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 114 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 146 2 8 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  114 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 146 2 7 57 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 146 (accept_3_2 13
  114 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 146 2 6 57 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 146
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 114 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 146 2 5 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 114 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 114 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 146 2 4 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 146 (accept_3_2 7 114 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 114 146 2 3 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 114 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 114 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 146 2 2 57 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 3
  114 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 114 146 2 1 57 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 146 (accept_3_2 1
  114 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114 146))))))))))))))))))))))))))))))))) (allB_succ' 34 113
  146 (Eq.refl Bool.true) (allA_succ_of_accept 33 113 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 146 (accept_3_2 31 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 146 (Polychromatic418967fa.accept_10_9_3_6_1_686 29 113 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 146 (accept_3_2 28 113 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 146
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 146 (accept_3_2 25 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 146 (accept_3_2 22 113 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 146 (accept_3_2 19 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 113 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 146 (accept_3_2 16 113 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 146
  (Polychromatic418967fa.accept_19_14_18_13_1_7823 14 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 113 146 (accept_3_2 13 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 113 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 146 (accept_3_2 10 113 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 146
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 146 (accept_3_2 7 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 146 (accept_3_2 4 113 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 146
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 146 (accept_3_2 1 113 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  146)))))))))))))))))))))))))))))))))) (allB_succ' 35 112 146 (Eq.refl Bool.true) (allA_of_3_0 35 112 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 111 146 (Eq.refl Bool.true) (allA_succ_of_accept 35 111 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 146 (accept_3_2 34 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 146 (accept_3_2 31 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 111 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 146 (accept_3_2 28 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 146 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 146 (accept_3_2 25 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 146 (accept_3_2 22 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 146 (Polychromatic418967fa.accept_15_5_6_11_1_854 20 111 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 146 (accept_3_2 19 111 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 111
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 146 (accept_3_2 16 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 146 (accept_3_2 13 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 111 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 146 (accept_3_2 10 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 146 (accept_3_2 7 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 146 (accept_3_2 4 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 146 (Polychromatic418967fa.accept_15_3_6_11_1_855 3 111 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 2 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 146 (accept_3_2 1 111 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 146)))))))))))))))))))))))))))))))))))) (allB_succ' 37 110 146 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 110 146 2 18 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 146 (Polychromatic418967fa.accept_13_9_6_3_1_1514 35 110 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 146 2 17 55 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 146
  (Polychromatic418967fa.accept_19_14_15_13_1_4898 33 110 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 110 146 2 16 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 110 146 (accept_3_2 31 110 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 146 2 15 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 110 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 146 2 14 55 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 146
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 110 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 146 2 13 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 146 (accept_3_2 25 110 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 146 2 12 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 146 (Polychromatic418967fa.accept_13_10_6_3_1_1515 23 110 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 146 2 11 55 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 146
  (Polychromatic418967fa.accept_15_6_5_11_1_2378 21 110 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 146 2 10 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 146 (accept_3_2 19 110 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 146 2 9 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 146 (Polychromatic418967fa.accept_15_2_5_11_1_1563 17 110 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 146 2 8 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  110 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 146 2 7 55 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 146 (accept_3_2 13
  110 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 146 2 6 55 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 110 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 146 2 5 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 146 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 110 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 146 2 4 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 146 (accept_3_2 7 110 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 146 2 3 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 146 (Polychromatic418967fa.accept_13_5_6_3_1_868 5 110 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 146 2 2 55 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 146 (Polychromatic418967fa.accept_23_3_18_8_1_7822
  3 110 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 146 2 1 55 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 146 (accept_3_2 1
  110 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110 146))))))))))))))))))))))))))))))))))))) (allB_succ' 38
  109 146 (Eq.refl Bool.true) (allA_of_3_0 38 109 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 108 146
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 146 2 19 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 146 (accept_3_2 37 108 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 108 146 2 18 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 108 146 (Polychromatic418967fa.accept_48_35_12_2_1_7821 35 108 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 146 2 17 54 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 146
  (Polychromatic418967fa.accept_10_3_8_6_1_326 33 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 108 146 2 16 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 108 146 (accept_3_2 31 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 146 2 15 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 146 (Polychromatic418967fa.accept_15_14_3_11_1_850 29 108 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 146 2 14 54 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 146
  (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 108 146 2 13 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 108 146 (accept_3_2 25 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 146 2 12 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 108 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 108 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 146 2 11 54 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 146
  (Polychromatic418967fa.accept_15_6_3_11_1_848 21 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 108 146 2 10 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 108 146 (accept_3_2 19 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 146 2 9 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 146 (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 108 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 146 2 8 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 108 146
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 15 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 108 146 2 7 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 108 146 (accept_3_2 13 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 108 146 2 6 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 108 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 146 2 5 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 108
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 108 146 2 4 54 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 108 146 (accept_3_2 7
  108 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 146 2 3 54 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 146
  (Polychromatic418967fa.accept_31_5_15_22_1_7820 5 108 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 146 2 2 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 108 146 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 108 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 146 2 1 54 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 146 (accept_3_2 1 108 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 108 146))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 107 146 (Eq.refl Bool.true)
  (allA_succ_of_accept 39 107 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 107 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 146 (accept_3_2 37 107 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 36
  107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 146
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 146 (accept_3_2 34 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 107 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 146 (accept_3_2 31 107 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 146 (accept_3_2 28 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 146 (Polychromatic418967fa.accept_18_8_17_2_1_1557 26 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 146 (accept_3_2 25 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 146 (accept_3_2 22 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 146 (accept_3_2 19 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 107 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 146 (accept_3_2 16 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 146 (accept_3_2 13 107 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 146
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 146 (accept_3_2 10 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 146 (accept_3_2 7 107 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 146 (accept_3_2 4 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 146 (Polychromatic418967fa.accept_22_2_19_14_1_7819 2 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 146 (accept_3_2 1 107 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 107 146)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 106 146
  (Eq.refl Bool.true) (allA_of_3_0 41 106 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 105 146 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 105 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 146 (accept_3_2 40 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 105 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 146
  (Polychromatic418967fa.accept_16_6_9_2_1_6518 38 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 146 (accept_3_2 37 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 146 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 146 (accept_3_2 34 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 146 (Polychromatic418967fa.accept_13_7_1_3_1_1523 33 105 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 146 (accept_3_2 31 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 146 (accept_3_2 28 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 105 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 146 (accept_3_2 25 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 146 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 146 (accept_3_2 22 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 105 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 146
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 146 (accept_3_2 19 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 146 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 146 (accept_3_2 16 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 105 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 146 (accept_3_2 13 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 146 (accept_3_2 10 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 146 (Polychromatic418967fa.accept_10_9_5_6_1_691 9 105 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 146 (accept_3_2 7 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 146 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 146 (accept_3_2 4 105 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 105 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 146
  (Polychromatic418967fa.accept_13_2_1_3_1_419 2 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 146 (accept_3_2 1 105 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  146)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 104 146 (Eq.refl Bool.true) (allA_succ_of_gcd 42 104 146
  2 21 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104
  146 (Polychromatic418967fa.accept_11_8_5_3_1_694 41 104 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 104 146 2 20 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 104 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 104 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 104 146 2 19 52 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 104 146 (accept_3_2 37 104 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 104 146 2 18 52 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 104 146
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 104 146 2 17 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 104 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 104 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 146 2 16 52 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 146 (accept_3_2 31 104 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 146 2 15 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 146 (Polychromatic418967fa.accept_12_5_8_2_1_309
  29 104 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 146 2 14 52 73
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 146
  (Polychromatic418967fa.accept_15_12_14_11_1_4375 27 104 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 146 2 13 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 146 (accept_3_2 25 104 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 146 2 12 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 146 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 104 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 146 2 11 52 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 146
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 104 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 146 2 10 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 146 (accept_3_2 19 104 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 146 2 9 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 146 2 8 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  104 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 146 2 7 52 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 146 (accept_3_2 13
  104 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 146 2 6 52 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 146
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 104 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 146 2 5 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 146 (Polychromatic418967fa.accept_29_9_17_1_1_7818 9 104 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 146 2 4 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 146 (accept_3_2 7 104 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 146 2 3 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 146 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 104 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 146 2 2 52 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  104 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 146 2 1 52 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 146 (accept_3_2 1
  104 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104 146)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 103 146 (Eq.refl Bool.true) (allA_of_3_0 44 103 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 102 146 (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 146 2 22 51 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 146 (accept_3_2 43 102 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 146 2 21 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  102 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 146 2 20 51 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 146
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 146 2 19 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 146 (accept_3_2 37 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 146 2 18 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 146 2 17 51 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 146
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 146 2 16 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 146 (accept_3_2 31 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 146 2 15 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 146 (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 102 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 146 2 14 51 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 146
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 146 2 13 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 146 (accept_3_2 25 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 146 2 12 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 102 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 146 2 11 51 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 146
  (Polychromatic418967fa.accept_10_1_2_6_1_638 21 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 146 2 10 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 146 (accept_3_2 19 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 146 2 9 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 102 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 146 2 8 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 15
  102 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 146 2 7 51 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 146 (accept_3_2 13
  102 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 146 2 6 51 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 146
  (Polychromatic418967fa.accept_10_1_2_6_1_638 11 102 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 102 146 2 5 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 102 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 102 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 146 2 4 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 146 (accept_3_2 7 102 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 102 146 2 3 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 102 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 102 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 146 2 2 51 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  102 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 102 146 2 1 51 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 146 (accept_3_2 1
  102 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102 146)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 101 146 (Eq.refl Bool.true) (allA_succ_of_accept 45 101 146 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 146 (accept_3_2 43 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 146 (Polychromatic418967fa.accept_13_2_10_3_1_1538 41 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 146 (accept_3_2 40 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 101 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 146
  (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 146 (accept_3_2 37 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 146 (Polychromatic418967fa.accept_19_17_6_13_1_6334 36 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 101 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 146 (accept_3_2 34 101 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 146
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 146 (accept_3_2 31 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 146 (Polychromatic418967fa.accept_16_13_5_2_1_2131 29 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 146 (accept_3_2 28 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 101 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 146
  (Polychromatic418967fa.accept_17_9_16_10_1_362 26 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 146 (accept_3_2 25 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 146 (Polychromatic418967fa.accept_13_11_10_3_1_3020 24 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 101 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 146 (accept_3_2 22 101 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 146 (accept_3_2 19 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 146 (Polychromatic418967fa.accept_10_7_1_6_1_673 17 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 146 (accept_3_2 16 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 101 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 146
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 101 146 (accept_3_2 13 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 101 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 101 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 101 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 146 (accept_3_2 10 101 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 146 (accept_3_2 7 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 146 (Polychromatic418967fa.accept_13_6_10_3_1_897 6 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 146 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 101 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 146 (accept_3_2 4 101 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 101 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 146 (accept_3_2 1 101 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  146)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 100 146 (Eq.refl Bool.true) (allA_of_3_0 47 100 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 99 146 (Eq.refl Bool.true) (allA_succ_of_accept 47 99 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 99 146 (accept_3_2 46 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  99 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 99 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 99 146 (accept_3_2 43 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 99 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 99 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 99 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 99 146 (accept_3_2 40 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  99 146 (Polychromatic418967fa.accept_17_5_14_10_1_2831 39 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 99 146 (Polychromatic418967fa.accept_16_6_3_2_1_3096 38 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 99 146 (accept_3_2 37 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 99 146 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 99 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 99 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 99 146 (accept_3_2 34 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  99 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 99 146 (Polychromatic418967fa.accept_15_2_9_11_1_1551 32 99 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 99 146 (accept_3_2 31 99 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 99 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 99 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 99 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 99 146 (accept_3_2 28 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  99 146 (Polychromatic418967fa.accept_19_8_4_13_1_4912 27 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 99 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 99 146 (accept_3_2 25 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 99 146 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 99 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 99 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 99 146 (accept_3_2 22 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  99 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 99 146 (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 99 146 (accept_3_2 19 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 99 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 99 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 99 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 99 146 (accept_3_2 16 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  99 146 (Polychromatic418967fa.accept_10_5_9_6_1_697 15 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 99 146 (Polychromatic418967fa.accept_19_14_4_13_1_7779 14 99 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 99 146 (accept_3_2 13 99 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 99 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 99 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 99 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 99 146 (accept_3_2 10 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  99 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 99 146 (Polychromatic418967fa.accept_19_8_4_13_1_4912 8 99 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 99 146 (accept_3_2 7 99 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 99 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 99 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 99 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 99
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 146 (accept_3_2 4 99 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 99 146 (Polychromatic418967fa.accept_10_3_9_6_1_94 3
  99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 146
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 99 146 (accept_3_2 1 99 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  146)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 98 146 (Eq.refl Bool.true) (allA_succ_of_gcd 48 98
  146 2 24 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  98 146 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 98 146 2 23 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 98 146 (Polychromatic418967fa.accept_19_7_3_13_1_3492 45 98 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 98 146 2 22 49 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 98 146 (accept_3_2 43 98 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98 146 2 21 49 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 98 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 98 146 2 20 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 98 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 98 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 146 2 19 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 146 (accept_3_2 37 98 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 146 2 18 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 146 (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 98 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 98 146 2 17 49 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 98 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 98 146 2 16 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 98 146 (accept_3_2 31 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98
  146 2 15 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  98 146 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 98 146 2 14 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 98 146 (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 98 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 98 146 2 13 49 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 98 146 (accept_3_2 25 98 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98 146 2 12 49 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 98 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 98 146 2 11 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 98 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 98 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 146 2 10 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 146 (accept_3_2 19 98 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 146 2 9 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 98 146 (Polychromatic418967fa.accept_13_4_7_3_1_92 17 98 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 146 2 8 49 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 146 2 7 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 146 (accept_3_2 13 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  146 2 6 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 146 (Polychromatic418967fa.accept_13_11_7_3_1_894 11 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 146 2 5 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 146 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9 98 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 146 2 4 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 146 (accept_3_2 7 98 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 146 2 3 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 146 2 2 49 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 146
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 146 2 1 49 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 146 (accept_3_2 1 98 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  146))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 97 146 (Eq.refl Bool.true) (allA_of_3_0 50 97 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 96 146 (Eq.refl Bool.true) (allA_succ_of_gcd 50 96 146 2 25 48
  73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 96 146
  (accept_3_2 49 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96 146 2 24 48 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 96 146
  (Polychromatic418967fa.accept_13_8_5_3_1_427 47 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 96 146 2 23 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 96 146 (Polychromatic418967fa.accept_13_6_5_3_1_426 45 96 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 146 2 22 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 146 (accept_3_2 43 96 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 146 2 21 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 96 146 2 20 48 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 96 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 96 146 2 19 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 96 146 (accept_3_2 37 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96
  146 2 18 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  96 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 96 146 2 17 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 96 146 (Polychromatic418967fa.accept_15_3_6_11_1_855 33 96 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 96 146 2 16 48 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 96 146 (accept_3_2 31 96 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96 146 2 15 48 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 96 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 96 146 2 14 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 96 146 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 96 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 146 2 13 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 146 (accept_3_2 25 96 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 146 2 12 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 96 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 146 2 11 48 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 146
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 146 2 10 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 146 (accept_3_2 19 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  146 2 9 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 146 2 8 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 96 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 146 2 7 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 146 (accept_3_2 13 96 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 146 2 6 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 96 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 96 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 146 2 5 48 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 146
  (Polychromatic418967fa.accept_13_9_5_3_1_428 9 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 146 2 4 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 146 (accept_3_2 7 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 146
  2 3 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  146 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 146 2 2 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 146 2 1 48 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 146 (accept_3_2 1 96 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 146))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 95 146 (Eq.refl
  Bool.true) (allA_succ_of_accept 51 95 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 146
  (Polychromatic418967fa.accept_20_10_15_6_1_2149 50 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 95 146 (accept_3_2 49 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  95 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 95 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 146 (accept_3_2 46 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 95 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 95 146 (accept_3_2 43 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  95 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 95 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 146 (accept_3_2 40 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 146 (accept_3_2 37 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 146 (Polychromatic418967fa.accept_15_6_5_11_1_2378 36 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 146 (accept_3_2 34 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 95 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 146
  (Polychromatic418967fa.accept_11_10_7_3_1_3679 32 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 146 (accept_3_2 31 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 146 (accept_3_2 28 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 146
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 146 (accept_3_2 25 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 146 (accept_3_2 22 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 95 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 146
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 146 (accept_3_2 19 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 146 (Polychromatic418967fa.accept_21_18_11_20_1_3154 18 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 146 (accept_3_2 16 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 146
  (Polychromatic418967fa.accept_10_4_5_6_1_651 14 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 146 (accept_3_2 13 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 146 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 146 (accept_3_2 10 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 95 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 146
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 146 (accept_3_2 7 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  146 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 95 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 146 (accept_3_2 4 95 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  95 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 146 (accept_3_2 1 95 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95 146))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 94 146 (Eq.refl Bool.true) (allA_of_3_0 53 94 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  54 93 146 (Eq.refl Bool.true) (allA_succ_of_accept 53 93 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 146 (accept_3_2 52 93 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 93 146 (accept_3_2 49 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  93 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 146 (accept_3_2 46 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 93 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 93 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 93 146 (accept_3_2 43 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  93 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 93 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 146 (accept_3_2 40 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 93 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 93 146 (accept_3_2 37 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  93 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 146 (accept_3_2 34 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 93 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 93 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 146
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 93 146 (accept_3_2 31 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  93 146 (Polychromatic418967fa.accept_11_8_5_3_1_694 30 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 93 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 146 (accept_3_2 28 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 93 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 93 146 (accept_3_2 25 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  93 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 146 (accept_3_2 22 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 93 146 (Polychromatic418967fa.accept_15_6_3_11_1_848 21 93 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 146
  (Polychromatic418967fa.accept_27_20_12_11_1_7817 20 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 93 146 (accept_3_2 19 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 93 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 93 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 93 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 146 (accept_3_2 16 93 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 146 (accept_3_2 13 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 146 (Polychromatic418967fa.accept_13_12_2_3_1_1527 12 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 146 (accept_3_2 10 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 146 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 93 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 146 (accept_3_2 7 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  146 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 146 (accept_3_2 4 93 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 93 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 146 (Polychromatic418967fa.accept_17_2_8_10_1_2870
  2 93 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 146 (accept_3_2 1 93
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93 146))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 55 92 146 (Eq.refl Bool.true) (allA_succ_of_gcd 54 92 146 2 27 46 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 92 146
  (Polychromatic418967fa.accept_12_5_8_2_1_309 53 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 92 146 2 26 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 92 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 92 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 146 2 25 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 146 (accept_3_2 49 92 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 146 2 24 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 92 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 92 146 2 23 46 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 92 146
  (Polychromatic418967fa.accept_13_6_1_3_1_1522 45 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 92 146 2 22 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 92 146 (accept_3_2 43 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92
  146 2 21 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  92 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 92 146 2 20 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 92 146 (Polychromatic418967fa.accept_15_9_2_11_1_2391 39 92 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 92 146 2 19 46 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 92 146 (accept_3_2 37 92 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92 146 2 18 46 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 92 146
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 92 146 2 17 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 92 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 92 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 146 2 16 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 146 (accept_3_2 31 92 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 146 2 15 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 146 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 92 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 146 2 14 46 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 146
  (Polychromatic418967fa.accept_20_7_12_6_1_2164 27 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 146 2 13 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 92 146 (accept_3_2 25 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92
  146 2 12 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  92 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 92 146 2 11 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 92 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 92 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 146 2 10 46 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 146 (accept_3_2 19 92 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 146 2 9 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 146 (Polychromatic418967fa.accept_12_5_8_2_1_309 17
  92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 146 2 8 46 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 146
  (Polychromatic418967fa.accept_13_2_1_3_1_419 15 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 146 2 7 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 146 (accept_3_2 13 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  146 2 6 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 146 2 5 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 92 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 146 2 4 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 146 (accept_3_2 7 92 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 146 2 3 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 92 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 146 2 2 46 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 146
  (Polychromatic418967fa.accept_17_3_7_10_1_3948 3 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 146 2 1 46 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 146 (accept_3_2 1 92 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 91 146 (Eq.refl Bool.true) (allA_of_3_0 56
  91 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 90 146 (Eq.refl Bool.true) (allA_succ_of_gcd 56 90 146
  2 28 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 90
  146 (accept_3_2 55 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90 146 2 27 45 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 90 146
  (Polychromatic418967fa.accept_19_15_14_13_1_2343 53 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 90 146 2 26 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 90 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 90 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 146 2 25 45 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 146 (accept_3_2 49 90 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 146 2 24 45 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 146
  (Polychromatic418967fa.accept_17_13_5_10_1_2839 47 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 90 146 2 23 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 90 146 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 90 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 146 2 22 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 146 (accept_3_2 43 90 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 146 2 21 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 146 (Polychromatic418967fa.accept_13_2_12_3_1_415 41 90 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 146 2 20 45 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 146
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 146 2 19 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 90 146 (accept_3_2 37 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90
  146 2 18 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  90 146 (Polychromatic418967fa.accept_13_9_12_3_1_907 35 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 90 146 2 17 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 90 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 90 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 146 2 16 45 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 146 (accept_3_2 31 90 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 146 2 15 45 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 146
  (Polychromatic418967fa.accept_17_12_5_10_1_5160 29 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 90 146 2 14 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 90 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 90 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 146 2 13 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 146 (accept_3_2 25 90 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 146 2 12 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 146 (Polychromatic418967fa.accept_11_1_2_3_1_688 23 90 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 90 146 2 11 45 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 90 146
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 90 146 2 10 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 90 146 (accept_3_2 19 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90
  146 2 9 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  90 146 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 90 146 2 8 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 90 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 90 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 90 146 2 7 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 90 146 (accept_3_2 13 90 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90 146 2 6 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 90 146 (Polychromatic418967fa.accept_21_11_6_20_1_4589 11 90 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 90 146 2 5 45 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 90 146
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 90 146 2 4 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 90 146 (accept_3_2 7 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 146
  2 3 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 90
  146 (Polychromatic418967fa.accept_19_5_14_13_1_7816 5 90 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 90 146 2 2 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 90 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 90 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 90 146 2 1 45 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 90 146 (accept_3_2 1 90 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 90 146))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 89 146
  (Eq.refl Bool.true) (allA_succ_of_accept 57 89 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 89 146 (accept_3_2 55 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  89 146 (Polychromatic418967fa.accept_13_2_11_3_1_873 54 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 89 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 146 (accept_3_2 52 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 89 146 (accept_3_2 49 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  89 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 146 (accept_3_2 46 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 89 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 89 146 (accept_3_2 43 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  89 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 89 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 146 (accept_3_2 40 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 146
  (Polychromatic418967fa.accept_16_6_9_2_1_6518 38 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 89 146 (accept_3_2 37 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  89 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 146 (accept_3_2 34 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 89 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 89 146 (accept_3_2 31 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  89 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 89 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 89 146 (accept_3_2 28 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 89 146
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 26 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 89 146 (accept_3_2 25 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  89 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 89 146 (accept_3_2 22 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 89 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 89 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 89 146 (accept_3_2 19 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  89 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 89 146 (Polychromatic418967fa.accept_16_1_9_2_1_4161 17 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 89 146 (accept_3_2 16 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 89 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 89 146 (accept_3_2 13 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  89 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 89 146 (accept_3_2 10 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 89 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 89 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 89 146 (accept_3_2 7 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 89
  146 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 89 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 89 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 89 146 (accept_3_2 4 89 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 89 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 89 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 89 146 (Polychromatic418967fa.accept_11_2_1_3_1_683 2
  89 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 146 (accept_3_2 1 89 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 89 146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 59 88 146 (Eq.refl Bool.true) (allA_of_3_0 59 88 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  60 87 146 (Eq.refl Bool.true) (allA_succ_of_accept 59 87 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 146 (accept_3_2 58 87 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 146
  (Polychromatic418967fa.accept_20_16_7_6_1_7815 56 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 146 (accept_3_2 55 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 146 (accept_3_2 52 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 87 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 146 (accept_3_2 49 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 146 (accept_3_2 46 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 87 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 146 (accept_3_2 43 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 146 (accept_3_2 40 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 87 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 146
  (Polychromatic418967fa.accept_13_12_9_3_1_3047 38 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 146 (accept_3_2 37 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 146 (Polychromatic418967fa.accept_19_17_11_13_1_4840 36 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 146 (accept_3_2 34 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 87 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 146
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 146 (accept_3_2 31 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 146 (accept_3_2 28 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 146 (Polychromatic418967fa.accept_16_11_7_2_1_4185 27 87 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 146 (accept_3_2 25 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 146 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 146 (accept_3_2 22 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 87 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 146
  (Polychromatic418967fa.accept_13_7_9_3_1_1504 20 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 146 (accept_3_2 19 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 146 (accept_3_2 16 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 146 (Polychromatic418967fa.accept_13_2_9_3_1_2212 15 87 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 146 (accept_3_2 13 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 146 (accept_3_2 10 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 87 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 146 (accept_3_2 7 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  146 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 87 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 87 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 146 (accept_3_2 4 87 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 87 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 87
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 146 (accept_3_2 1 87 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87 146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 61 86 146 (Eq.refl Bool.true) (allA_succ_of_gcd 60 86 146 2 30 43 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 86 146 2 29 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 86 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 86 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 86 146 2 28 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 86 146 (accept_3_2 55 86 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86 146 2 27 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 86 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 86 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 86 146 2 26 43 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 86 146
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 86 146 2 25 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 86 146 (accept_3_2 49 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86
  146 2 24 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  86 146 (Polychromatic418967fa.accept_18_11_14_2_1_5058 47 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 86 146 2 23 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 86 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 86 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 146 2 22 43 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 146 (accept_3_2 43 86 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 146 2 21 43 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 146
  (Polychromatic418967fa.accept_16_9_6_2_1_3101 41 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 86 146 2 20 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 86 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 86 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 86 146 2 19 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 86 146 (accept_3_2 37 86 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86 146 2 18 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 86 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 86 146 2 17 43 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 86 146
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 86 146 2 16 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 86 146 (accept_3_2 31 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86
  146 2 15 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  86 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 86 146 2 14 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 86 146 (Polychromatic418967fa.accept_16_11_6_2_1_4155 27 86 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 146 2 13 43 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 146 (accept_3_2 25 86 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 146 2 12 43 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 146
  (Polychromatic418967fa.accept_19_4_10_13_1_7814 23 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 86 146 2 11 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 86 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 86 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 86 146 2 10 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 86 146 (accept_3_2 19 86 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86 146 2 9 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 86 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 86 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 86 146 2 8 43 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 86 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 86 146 2 7 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 86 146 (accept_3_2 13 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86
  146 2 6 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  86 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 86 146 2 5 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 86 146 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 86 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 86 146 2 4 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 86 146 (accept_3_2 7 86 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 146 2 3 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 86 146 (Polychromatic418967fa.accept_13_5_8_3_1_1535 5 86 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 86 146 2 2 43 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 86 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 86 146 2 1 43 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 86 146 (accept_3_2 1 86 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 86
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 85 146 (Eq.refl Bool.true)
  (allA_of_3_0 62 85 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 84 146 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 84 146 2 31 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 84 146 (accept_3_2 61 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84
  146 2 30 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  84 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 84 146 2 29 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 84 146 (Polychromatic418967fa.accept_13_5_6_3_1_868 57 84 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 84 146 2 28 42 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 84 146 (accept_3_2 55 84 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84 146 2 27 42 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 84 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 84 146 2 26 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 84 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 146 2 25 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 146 (accept_3_2 49 84 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 146 2 24 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 146 (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 84 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 84 146 2 23 42 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 84 146
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 84 146 2 22 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 84 146 (accept_3_2 43 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84
  146 2 21 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  84 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 84 146 2 20 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 84 146 (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 84 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 84 146 2 19 42 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 84 146 (accept_3_2 37 84 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84 146 2 18 42 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 84 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 84 146 2 17 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 84 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 146 2 16 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 146 (accept_3_2 31 84 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 146 2 15 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 146 (Polychromatic418967fa.accept_22_7_18_14_1_7813 29 84
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 84 146 2 14 42 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 84 146
  (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 84 146 2 13 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 84 146 (accept_3_2 25 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84
  146 2 12 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  84 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 84 146 2 11 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 84 146 (Polychromatic418967fa.accept_11_10_7_3_1_3679 21 84 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 84 146 2 10 42 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 84 146 (accept_3_2 19 84 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84 146 2 9 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 84 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 84 146 2 8 42 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 84 146
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 84 146 2 7 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 84 146 (accept_3_2 13 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84
  146 2 6 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  84 146 (Polychromatic418967fa.accept_25_11_9_21_1_7812 11 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 84 146 2 5 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 84 146 (Polychromatic418967fa.accept_13_9_6_3_1_1514 9 84 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 84 146 2 4 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 84 146 (accept_3_2 7 84 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 146 2 3 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 84 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 84 146 2 2 42 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 84 146
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 3 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 84 146 2 1 42 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 84 146 (accept_3_2 1 84 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 84
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 83 146 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 83 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 146 (Polychromatic418967fa.accept_19_5_7_13_1_4919 62 83
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 83 146 (accept_3_2 61 83 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 83 146 (Polychromatic418967fa.accept_13_8_5_3_1_427
  60 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 83 146
  (Polychromatic418967fa.accept_10_9_3_6_1_686 59 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 83 146 (accept_3_2 58 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  83 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 83 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 83 146 (accept_3_2 55 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 83 146 (Polychromatic418967fa.accept_13_2_5_3_1_406 54 83 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 83 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 83 146 (accept_3_2 52 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  83 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 83 146 (Polychromatic418967fa.accept_13_11_5_3_1_889 50 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 83 146 (accept_3_2 49 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 83 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 83 146
  (Polychromatic418967fa.accept_10_7_3_6_1_644 47 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 83 146 (accept_3_2 46 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  83 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 83 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 83 146 (accept_3_2 43 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 83 146 (Polychromatic418967fa.accept_11_9_6_3_1_1668 42 83 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 83 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 83 146 (accept_3_2 40 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  83 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 83 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 38 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 83 146 (accept_3_2 37 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 83 146 (Polychromatic418967fa.accept_17_2_15_10_1_5171 36 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 83 146
  (Polychromatic418967fa.accept_13_9_5_3_1_428 35 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 83 146 (accept_3_2 34 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  83 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 83 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 83 146 (accept_3_2 31 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 83 146 (Polychromatic418967fa.accept_11_8_6_3_1_661 30 83 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 83 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 83 146 (accept_3_2 28 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  83 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 83 146 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 83 146 (accept_3_2 25 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 83 146 (Polychromatic418967fa.accept_13_11_5_3_1_889 24 83 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 83 146
  (Polychromatic418967fa.accept_19_4_7_13_1_3480 23 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 83 146 (accept_3_2 22 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  83 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 83 146 (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 83 146 (accept_3_2 19 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 83 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 83 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 83 146 (accept_3_2 16 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  83 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 83 146 (Polychromatic418967fa.accept_13_1_5_3_1_888 14 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 83 146 (accept_3_2 13 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 83 146 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 83 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 83 146
  (Polychromatic418967fa.accept_13_11_5_3_1_889 11 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 83 146 (accept_3_2 10 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  83 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 83 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 8 83 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 83 146 (accept_3_2 7 83 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 83 146 (Polychromatic418967fa.accept_13_6_5_3_1_426 6 83 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 83 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 83
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 146 (accept_3_2 4 83 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 146
  (Polychromatic418967fa.accept_13_2_5_3_1_406 2 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 146 (accept_3_2 1 83 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 82 146 (Eq.refl Bool.true)
  (allA_of_3_0 65 82 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 81 146 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 81 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 146 (accept_3_2 64 81 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 146 (Polychromatic418967fa.accept_10_2_1_6_1_634
  62 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 81 146 (accept_3_2 61
  81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 81 146
  (Polychromatic418967fa.accept_16_12_1_2_1_2163 60 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 81 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 146 (accept_3_2 58 81 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 81 146 (Polychromatic418967fa.accept_10_7_1_6_1_673 57 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 146
  (Polychromatic418967fa.accept_17_5_13_10_1_3949 56 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 146 (accept_3_2 55 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 146 (accept_3_2 52 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 81 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 146
  (Polychromatic418967fa.accept_15_5_6_11_1_854 50 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 146 (accept_3_2 49 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 146 (Polychromatic418967fa.accept_15_3_6_11_1_855 48 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 146 (accept_3_2 46 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 81 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 146 (accept_3_2 43 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 146 (accept_3_2 40 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 81 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 146 (accept_3_2 37 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 146 (Polychromatic418967fa.accept_20_16_1_6_1_6196 36 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 146 (accept_3_2 34 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 81 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 146
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 81 146 (accept_3_2 31 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  81 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 81 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 146 (accept_3_2 28 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 81 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 146
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 146 (accept_3_2 25 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 146 (accept_3_2 22 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 146 (Polychromatic418967fa.accept_18_3_9_2_1_5053 21 81 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 146
  (Polychromatic418967fa.accept_15_5_6_11_1_854 20 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 146 (accept_3_2 19 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 146 (Polychromatic418967fa.accept_11_7_4_3_1_302 18 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 146 (accept_3_2 16 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 81 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 146
  (Polychromatic418967fa.accept_17_14_13_10_1_3936 14 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 81 146 (accept_3_2 13 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 81 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 81 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 81 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 146 (accept_3_2 10 81 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 9
  81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 146
  (Polychromatic418967fa.accept_19_8_5_13_1_7800 8 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 146 (accept_3_2 7 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  146 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 146 (accept_3_2 4 81 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 81 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  81 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 146 (accept_3_2 1 81 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 80 146 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 80 146 2 33 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 80 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 80 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 146 2 32 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 146 (Polychromatic418967fa.accept_13_11_2_3_1_883
  63 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 80 146 2 31 40 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 80 146 (accept_3_2 61
  80 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80 146 2 30 40 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 80 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 80 146 2 29 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 80 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 80 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 146 2 28 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 80 146 (accept_3_2 55 80 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80 146 2 27 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 80 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 80 146 2 26 40 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 80 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 80 146 2 25 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 80 146 (accept_3_2 49 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80
  146 2 24 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  80 146 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 80 146 2 23 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 80 146 (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 80 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 80 146 2 22 40 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 80 146 (accept_3_2 43 80 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80 146 2 21 40 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 80 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 80 146 2 20 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 80 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 80 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 146 2 19 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 146 (accept_3_2 37 80 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 146 2 18 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 146 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 80 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 146 2 17 40 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 146 2 16 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 146 (accept_3_2 31 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  146 2 15 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 146 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 146 2 14 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 80 146 (Polychromatic418967fa.accept_13_1_2_3_1_911 27 80 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 146 2 13 40 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 146 (accept_3_2 25 80 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 146 2 12 40 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 80 146 2 11 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 80 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 80 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 80 146 2 10 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 80 146 (accept_3_2 19 80 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80 146 2 9 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 80 146 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 80 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 80 146 2 8 40 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 80 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 80 146 2 7 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 80 146 (accept_3_2 13 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80
  146 2 6 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  80 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 80 146 2 5 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 80 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 80 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 80 146 2 4 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 80 146 (accept_3_2 7 80 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 146 2 3 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 80 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 80 146 2 2 40 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 80 146
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 80 146 2 1 40 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 80 146 (accept_3_2 1 80 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 80
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 79 146 (Eq.refl Bool.true)
  (allA_of_3_0 68 79 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 78 146 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 78 146 2 34 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 78 146 (accept_3_2 67 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78
  146 2 33 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  78 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 78 146 2 32 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 78 146 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 78 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 78 146 2 31 39 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 78 146 (accept_3_2 61 78 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78 146 2 30 39 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 78 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 78 146 2 29 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 78 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 146 2 28 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 146 (accept_3_2 55 78 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 146 2 27 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 78 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 78 146 2 26 39 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 78 146
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 78 146 2 25 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 78 146 (accept_3_2 49 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78
  146 2 24 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  78 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 78 146 2 23 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 78 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 78 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 78 146 2 22 39 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 78 146 (accept_3_2 43 78 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78 146 2 21 39 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 78 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 78 146 2 20 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 78 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 78 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 146 2 19 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 146 (accept_3_2 37 78 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 146 2 18 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 78 146 2 17 39 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 78 146
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 78 146 2 16 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 78 146 (accept_3_2 31 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78
  146 2 15 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  78 146 (Polychromatic418967fa.accept_15_14_3_11_1_850 29 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 78 146 2 14 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 78 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 78 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 78 146 2 13 39 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 78 146 (accept_3_2 25 78 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78 146 2 12 39 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 78 146
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 78 146 2 11 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 78 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 146 2 10 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 146 (accept_3_2 19 78 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 146 2 9 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 78 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 78 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 146 2 8 39 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 146
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 146 2 7 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 146 (accept_3_2 13 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  146 2 6 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 146 (Polychromatic418967fa.accept_19_11_2_13_1_4907 11 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 146 2 5 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 78 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 146 2 4 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 146 (accept_3_2 7 78 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 146 2 3 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 78 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 146 2 2 39 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 146
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 146 2 1 39 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 146 (accept_3_2 1 78 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 77 146 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 77 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 77 146 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 77 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 146 (accept_3_2 67 77 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 66
  77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 146
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 65 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 146 (accept_3_2 64 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 146 (accept_3_2 61 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 146 (accept_3_2 58 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 146 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 146 (accept_3_2 55 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 146 (Polychromatic418967fa.accept_13_2_12_3_1_415 54 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 146
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 146 (accept_3_2 52 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 146 (Polychromatic418967fa.accept_14_8_7_6_1_1159 50 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 146 (accept_3_2 49 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 146 (accept_3_2 46 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 146 (accept_3_2 43 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 146
  (Polychromatic418967fa.accept_10_1_7_6_1_91 41 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 146 (accept_3_2 40 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 146 (Polychromatic418967fa.accept_21_17_14_20_1_7811 38 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 146 (accept_3_2 37 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 146 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 77 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 146 (accept_3_2 34 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 146 (Polychromatic418967fa.accept_12_8_5_2_1_746 32 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 146 (accept_3_2 31 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 146
  (Polychromatic418967fa.accept_14_1_7_6_1_3604 29 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 146 (accept_3_2 28 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 146 (accept_3_2 25 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 146 (accept_3_2 22 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 146 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 146 (accept_3_2 19 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 146 (Polychromatic418967fa.accept_17_1_9_10_1_1864 18 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 146
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 146 (accept_3_2 16 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 146 (Polychromatic418967fa.accept_19_14_1_13_1_7810 14 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 146 (accept_3_2 13 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 146 (accept_3_2 10 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 146 (accept_3_2 7 77 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 146
  (Polychromatic418967fa.accept_15_5_2_11_1_1596 5 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 146 (accept_3_2 4 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 77 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 146 (Polychromatic418967fa.accept_13_2_12_3_1_415 2 77 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 146 (accept_3_2 1 77 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 76
  146 (Eq.refl Bool.true) (allA_of_3_0 71 76 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 75 146 (Eq.refl
  Bool.true) (allA_succ_of_accept 71 75 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 146 (accept_3_2 70 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 146 (accept_3_2 67 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 66 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 146 (accept_3_2 64 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 146 (Polychromatic418967fa.accept_13_11_10_3_1_3020 63 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 146 (accept_3_2 61 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 146 (accept_3_2 58 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 146
  (Polychromatic418967fa.accept_24_8_3_2_1_7809 56 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 146 (accept_3_2 55 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 146 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 146 (accept_3_2 52 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 146 (accept_3_2 49 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 146 (Polychromatic418967fa.accept_17_14_7_10_1_7808 48 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 146 (accept_3_2 46 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 146 (accept_3_2 43 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 146 (accept_3_2 40 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 146
  (Polychromatic418967fa.accept_16_6_11_2_1_6485 38 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 146 (accept_3_2 37 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 146 (accept_3_2 34 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 146 (accept_3_2 31 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 146 (accept_3_2 28 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 146 (Polychromatic418967fa.accept_14_13_5_6_1_2747 27 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 146 (accept_3_2 25 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 146 (accept_3_2 22 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 146
  (Polychromatic418967fa.accept_13_7_10_3_1_1505 20 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 146 (accept_3_2 19 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 146 (accept_3_2 16 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 146 (accept_3_2 13 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 146 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 146 (accept_3_2 10 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 75 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 146 (accept_3_2 7 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  146 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 75 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 146 (accept_3_2 4 75 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 146 (Polychromatic418967fa.accept_17_3_7_10_1_3948 3 75 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 146 (Polychromatic418967fa.accept_13_2_10_3_1_1538
  2 75 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 146 (accept_3_2 1 75
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 74 146 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 74 146 2 36 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 74 146 (Polychromatic418967fa.accept_11_5_8_3_1_66 71 74 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 74 146 2 35 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 74 146 (Polychromatic418967fa.accept_20_9_14_6_1_320
  69 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 146 2 34 37 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 146 (accept_3_2 67
  74 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 146 2 33 37 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 74 146 2 32 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 74 146 (Polychromatic418967fa.accept_15_3_14_11_1_1579 63 74 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 74 146 2 31 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 74 146 (accept_3_2 61 74 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74 146 2 30 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 74 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 74 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 74 146 2 29 37 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 74 146
  (Polychromatic418967fa.accept_13_5_9_3_1_870 57 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 74 146 2 28 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 74 146 (accept_3_2 55 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74
  146 2 27 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  74 146 (Polychromatic418967fa.accept_19_15_17_13_1_4901 53 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 74 146 2 26 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 74 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 74 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 146 2 25 37 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 146 (accept_3_2 49 74 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 146 2 24 37 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 146
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 74 146 2 23 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 74 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 74 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 74 146 2 22 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 74 146 (accept_3_2 43 74 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74 146 2 21 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 74 146 (Polychromatic418967fa.accept_13_2_9_3_1_2212 41 74 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 74 146 2 20 37 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 74 146
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 39 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 74 146 2 19 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 74 146 (accept_3_2 37 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74
  146 2 18 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  74 146 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 74 146 2 17 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 74 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 74 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 146 2 16 37 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 146 (accept_3_2 31 74 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 146 2 15 37 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 146
  (Polychromatic418967fa.accept_17_12_6_10_1_7807 29 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 74 146 2 14 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 74 146 (Polychromatic418967fa.accept_11_5_8_3_1_66 27 74 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 74 146 2 13 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 74 146 (accept_3_2 25 74 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74 146 2 12 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 74 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 74 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 74 146 2 11 37 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 74 146
  (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 74 146 2 10 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 74 146 (accept_3_2 19 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74
  146 2 9 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  74 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 74 146 2 8 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 74 146 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 74 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 74 146 2 7 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 74 146 (accept_3_2 13 74 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74 146 2 6 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 74 146 (Polychromatic418967fa.accept_19_11_17_13_1_3458 11 74 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 74 146 2 5 37 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 74 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 74 146 2 4 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 74 146 (accept_3_2 7 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 146
  2 3 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 74
  146 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 74 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 74 146 2 2 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 74 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 74 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 74 146 2 1 37 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 74 146 (accept_3_2 1 74 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 74 146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73
  146 (allA_of_3_0 73 73 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 146 (allA_succ_of_accept 71 72 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 146 2 35 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 72 146 (Polychromatic418967fa.accept_13_4_7_3_1_92 69 72 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 146 2 34 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 146 (accept_3_2 67 72 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 146 2 33 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 146 (Polychromatic418967fa.accept_20_5_12_6_1_7806 65 72 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 146 2 32 36 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 146
  (Polychromatic418967fa.accept_11_8_6_3_1_661 63 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 146 2 31 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 146 (accept_3_2 61 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72
  146 2 30 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  72 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 72 146 2 29 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 72 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 72 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 146 2 28 36 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 146 (accept_3_2 55 72 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 146 2 27 36 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 146
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 146 2 26 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 51 72 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 146 2 25 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 146 (accept_3_2 49 72 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 146 2 24 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 146 (Polychromatic418967fa.accept_13_8_7_3_1_430 47 72 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 146 2 23 36 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 146 2 22 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 146 (accept_3_2 43 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  146 2 21 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  72 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 41 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 146 2 20 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 72 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 146 2 19 36 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 146 (accept_3_2 37 72 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 146 2 18 36 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 146
  (Polychromatic418967fa.accept_13_9_7_3_1_1531 35 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 72 146 2 17 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 72 146 (Polychromatic418967fa.accept_19_14_15_13_1_4898 33 72 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 72 146 2 16 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 72 146 (accept_3_2 31 72 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72 146 2 15 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 72 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 72 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 72 146 2 14 36 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 72 146
  (Polychromatic418967fa.accept_13_1_7_3_1_1503 27 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 72 146 2 13 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 72 146 (accept_3_2 25 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72
  146 2 12 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  72 146 (Polychromatic418967fa.accept_13_10_7_3_1_3041 23 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 72 146 2 11 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 72 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 21 72 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 72 146 2 10 36 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 72 146 (accept_3_2 19 72 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72 146 2 9 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 72 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 72 146 2 8 36 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 72 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 72 146 2 7 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 72 146 (accept_3_2 13 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72
  146 2 6 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  72 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 72 146 2 5 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 72 146 (Polychromatic418967fa.accept_11_9_6_3_1_1668 9 72 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 72 146 2 4 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 72 146 (accept_3_2 7 72 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 146 2 3 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 72 146 (Polychromatic418967fa.accept_20_5_12_6_1_7806 5 72 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 72 146 2 2 36 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 72 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 72 146 2 1 36 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 72 146 (accept_3_2 1 72 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 72
  146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 146 (allA_succ_of_accept 70
  71 146 (accept_3_2 70 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 71 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 69 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 71 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 71 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 146 (accept_3_2 67 71 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 71 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 65
  71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 71 146 (accept_3_2 64 71
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 71 146 (Polychromatic418967fa.accept_6_3_5_2_1_12
  63 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 71 146
  (Polychromatic418967fa.accept_10_2_1_6_1_634 62 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 71 146 (accept_3_2 61 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  71 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 71 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 71 146 (accept_3_2 58 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 71 146
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 71 146 (accept_3_2 55 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  71 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 71 146 (accept_3_2 52 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 71 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 71 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 71 146 (accept_3_2 49 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  71 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 71 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 71 146 (accept_3_2 46 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 71 146
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 71 146 (accept_3_2 43 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  71 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 71 146 (accept_3_2 40 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 71 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 71 146
  (Polychromatic418967fa.accept_21_17_8_20_1_7805 38 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 71 146 (accept_3_2 37 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  71 146 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 71 146 (Polychromatic418967fa.accept_10_5_1_6_1_672 35 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 71 146 (accept_3_2 34 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 71 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 71 146 (accept_3_2 31 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  71 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 71 146 (accept_3_2 28 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 71 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 71 146
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 71 146 (accept_3_2 25 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  71 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 71 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 71 146 (accept_3_2 22 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 71 146
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 71 146 (accept_3_2 19 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  71 146 (Polychromatic418967fa.accept_13_5_6_3_1_868 18 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 71 146 (accept_3_2 16 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 71 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 71 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 71 146 (accept_3_2 13 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  71 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 71 146 (Polychromatic418967fa.accept_16_11_7_2_1_4185 11 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 71 146 (accept_3_2 10 71 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 71 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 71 146
  (Polychromatic418967fa.accept_11_8_5_3_1_694 8 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 71 146 (accept_3_2 7 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 71
  146 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 71 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 71 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 71 146 (accept_3_2 4 71 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 71 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 71 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  71 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 146 (accept_3_2 1 71 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 71
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 146 (allA_of_3_0 70 70 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 146 (allA_succ_of_accept 68 69 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 146 (accept_3_2 67 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 146 (accept_3_2 64 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 146 (accept_3_2 61 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 146 (Polychromatic418967fa.accept_17_9_1_10_1_2859 60 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 146 (accept_3_2 58 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 146
  (Polychromatic418967fa.accept_19_18_12_13_1_2311 56 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 69 146 (accept_3_2 55 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 69 146 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 69 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 69 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 146 (accept_3_2 52 69 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 146 (accept_3_2 49 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 146 (accept_3_2 46 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 146 (Polychromatic418967fa.accept_10_5_9_6_1_697 45 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 146 (accept_3_2 43 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 146 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 146 (accept_3_2 40 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 146
  (Polychromatic418967fa.accept_13_12_4_3_1_1528 38 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 146 (accept_3_2 37 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 146 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 146 (accept_3_2 34 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 146 (Polychromatic418967fa.accept_10_3_9_6_1_94 33 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 146 (accept_3_2 31 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 146 (accept_3_2 28 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 146 (accept_3_2 25 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 146 (Polychromatic418967fa.accept_17_7_1_10_1_2836 24 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 146 (accept_3_2 22 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 146
  (Polychromatic418967fa.accept_13_7_4_3_1_3064 20 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 146 (accept_3_2 19 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 146 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 146 (accept_3_2 16 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 146 (accept_3_2 13 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 146 (accept_3_2 10 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 146 (Polychromatic418967fa.accept_17_9_1_10_1_2859 9 69 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 146 (accept_3_2 7 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  146 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 146 (accept_3_2 4 69 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 69 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 146 (Polychromatic418967fa.accept_15_2_9_11_1_1551
  2 69 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 146 (accept_3_2 1 69
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 146 (allA_succ_of_accept 67 68
  146 (accept_3_2 67 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 146 2 33 34 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 146
  (Polychromatic418967fa.accept_12_5_8_2_1_309 65 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 146 2 32 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 146 (Polychromatic418967fa.accept_10_3_8_6_1_326 63 68 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 146 2 31 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 146 (accept_3_2 61 68 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 146 2 30 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 146 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 68 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 146 2 29 34 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 146 2 28 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 146 (accept_3_2 55 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  146 2 27 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 146 2 26 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 68 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 146 2 25 34 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 146 (accept_3_2 49 68 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 146 2 24 34 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 146
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 146 2 23 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 146 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 68 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 146 2 22 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 146 (accept_3_2 43 68 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 146 2 21 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 146 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 68 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 146 2 20 34 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 146 2 19 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 146 (accept_3_2 37 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  146 2 18 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 146 2 17 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 68 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 146 2 16 34 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 146 (accept_3_2 31 68 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 146 2 15 34 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 68 146 2 14 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 68 146 (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 68 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 68 146 2 13 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 68 146 (accept_3_2 25 68 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68 146 2 12 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 68 146 (Polychromatic418967fa.accept_10_3_8_6_1_326 23 68 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 68 146 2 11 34 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 68 146
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 68 146 2 10 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 68 146 (accept_3_2 19 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68
  146 2 9 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  68 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 68 146 2 8 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 68 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 68 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 68 146 2 7 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 68 146 (accept_3_2 13 68 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68 146 2 6 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 68 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 68 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 68 146 2 5 34 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 68 146
  (Polychromatic418967fa.accept_23_9_22_8_1_4318 9 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 68 146 2 4 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 68 146 (accept_3_2 7 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 146
  2 3 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 68
  146 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 68 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 68 146 2 2 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 68 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 68 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 68 146 2 1 34 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 68 146 (accept_3_2 1 68 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 68 146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 146
  (allA_of_3_0 67 67 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 146 (allA_succ_of_accept 65 66 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 65 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 146 2 32 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 63 66 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 146 2 31 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 146 (accept_3_2 61 66 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 146 2 30 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 66 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 146 2 29 33 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 146
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 146 2 28 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 146 (accept_3_2 55 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  146 2 27 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 146 2 26 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 66 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 146 2 25 33 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 146 (accept_3_2 49 66 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 146 2 24 33 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 146
  (Polychromatic418967fa.accept_15_2_6_11_1_1587 47 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 66 146 2 23 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 66 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 66 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 146 2 22 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 146 (accept_3_2 43 66 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 146 2 21 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 66 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 66 146 2 20 33 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 66 146
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 66 146 2 19 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 66 146 (accept_3_2 37 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66
  146 2 18 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  66 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 66 146 2 17 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 66 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 66 146 2 16 33 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 66 146 (accept_3_2 31 66 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66 146 2 15 33 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 66 146
  (Polychromatic418967fa.accept_19_10_9_13_1_7804 29 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 66 146 2 14 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 66 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 66 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 146 2 13 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 146 (accept_3_2 25 66 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 146 2 12 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 66 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 66 146 2 11 33 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 66 146
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 66 146 2 10 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 66 146 (accept_3_2 19 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66
  146 2 9 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  66 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 66 146 2 8 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 66 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 66 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 66 146 2 7 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 66 146 (accept_3_2 13 66 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66 146 2 6 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 66 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 66 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 66 146 2 5 33 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 66 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 66 146 2 4 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 66 146 (accept_3_2 7 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 146
  2 3 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 66
  146 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 66 146 2 2 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 66 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 66 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 66 146 2 1 33 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 66 146 (accept_3_2 1 66 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 66 146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 146
  (allA_succ_of_accept 64 65 146 (accept_3_2 64 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  65 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 65 146 (Polychromatic418967fa.accept_11_7_10_3_1_633 62 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 146 (accept_3_2 61 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 65 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 59 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 146 (accept_3_2 58 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 146 (Polychromatic418967fa.accept_12_8_5_2_1_746 56 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 146 (accept_3_2 55 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 146 (Polychromatic418967fa.accept_10_4_5_6_1_651 54 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 146
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 146 (accept_3_2 52 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 146 (accept_3_2 49 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 146 (Polychromatic418967fa.accept_21_6_2_20_1_7803 48 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 146 (accept_3_2 46 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 146 (Polychromatic418967fa.accept_10_4_5_6_1_651 44 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 146 (accept_3_2 43 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 146 (Polychromatic418967fa.accept_19_4_8_13_1_7802 42 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 146
  (Polychromatic418967fa.accept_10_1_5_6_1_649 41 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 146 (accept_3_2 40 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 146 (accept_3_2 37 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 146 (accept_3_2 34 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 146 (accept_3_2 31 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 146 (Polychromatic418967fa.accept_17_13_14_10_1_1847 30 65 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 146 (accept_3_2 28 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 146 (Polychromatic418967fa.accept_21_5_2_20_1_6081 26 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 146 (accept_3_2 25 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 65 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 146 (accept_3_2 22 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 146 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 146 (accept_3_2 19 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 146 (accept_3_2 16 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 146 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 146 (accept_3_2 13 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 146 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 146 (accept_3_2 10 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 146 (accept_3_2 7 65 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 146 (Polychromatic418967fa.accept_15_6_5_11_1_2378 6 65 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 146
  (Polychromatic418967fa.accept_17_5_14_10_1_2831 5 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 146 (accept_3_2 4 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 65 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 146 (Polychromatic418967fa.accept_15_2_5_11_1_1563 2 65 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 146 (accept_3_2 1 65 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 146
  (allA_of_3_0 64 64 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 146 (allA_succ_of_accept 62 63 146
  (Polychromatic418967fa.accept_13_10_11_3_1_1518 62 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 146 (accept_3_2 61 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 146 (Polychromatic418967fa.accept_11_5_8_3_1_66 60 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 146 (accept_3_2 58 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 146
  (Polychromatic418967fa.accept_17_5_12_10_1_3963 56 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 146 (accept_3_2 55 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 146 (accept_3_2 52 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 146 (Polychromatic418967fa.accept_15_6_3_11_1_848 51 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 146
  (Polychromatic418967fa.accept_11_6_8_3_1_2236 50 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 63 146 (accept_3_2 49 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  63 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 48 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 63 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 146 (accept_3_2 46 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 146
  (Polychromatic418967fa.accept_13_5_11_3_1_902 44 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 146 (accept_3_2 43 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 146 (accept_3_2 40 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 146 (Polychromatic418967fa.accept_10_9_3_6_1_686 39 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 146
  (Polychromatic418967fa.accept_10_8_3_6_1_685 38 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 146 (accept_3_2 37 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 146 (Polychromatic418967fa.accept_13_10_11_3_1_1518 36 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 146 (accept_3_2 34 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 146
  (Polychromatic418967fa.accept_23_9_17_8_1_7801 32 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 146 (accept_3_2 31 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 146 (accept_3_2 28 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 146 (Polychromatic418967fa.accept_10_7_3_6_1_644 27 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 146
  (Polychromatic418967fa.accept_19_7_6_13_1_6322 26 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 146 (accept_3_2 25 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 146 (Polychromatic418967fa.accept_18_6_9_2_1_1575 24 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 146 (accept_3_2 22 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 146
  (Polychromatic418967fa.accept_13_7_11_3_1_1540 20 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 146 (accept_3_2 19 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 146 (accept_3_2 16 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 146 (Polychromatic418967fa.accept_13_2_11_3_1_873 15 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 146
  (Polychromatic418967fa.accept_13_1_11_3_1_901 14 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 146 (accept_3_2 13 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 146 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 146 (accept_3_2 10 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 146
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 146 (accept_3_2 7 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  146 (Polychromatic418967fa.accept_11_6_8_3_1_2236 6 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 63 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 146 (accept_3_2 4 63 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 63 146 (Polychromatic418967fa.accept_16_3_15_2_1_6475 3 63 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 146
  (Polychromatic418967fa.accept_13_2_11_3_1_873 2 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 63 146 (accept_3_2 1 63 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 146 (allA_succ_of_accept 61 62 146
  (accept_3_2 61 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 146 2 30 31 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 146 2 29 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 62 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 146 2 28 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 146 (accept_3_2 55 62 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 146 2 27 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 146 (Polychromatic418967fa.accept_18_17_8_2_1_2622 53 62 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 146 2 26 31 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 146 2 25 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 146 (accept_3_2 49 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  146 2 24 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 146 (Polychromatic418967fa.accept_19_9_5_13_1_4867 47 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 146 2 23 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 146 (Polychromatic418967fa.accept_13_6_10_3_1_897 45 62 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 146 2 22 31 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 146 (accept_3_2 43 62 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 146 2 21 31 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 146 2 20 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 62 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 146 2 19 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 146 (accept_3_2 37 62 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 146 2 18 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 146 (Polychromatic418967fa.accept_15_5_2_11_1_1596 35 62 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 146 2 17 31 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 146 2 16 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 146 (accept_3_2 31 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  146 2 15 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 146 (Polychromatic418967fa.accept_19_10_5_13_1_6287 29 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 146 2 14 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 146 (Polychromatic418967fa.accept_19_8_5_13_1_7800 27 62 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 146 2 13 31 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 146 (accept_3_2 25 62 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 146 2 12 31 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 146 2 11 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 62 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 146 2 10 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 146 (accept_3_2 19 62 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 146 2 9 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 146 (Polychromatic418967fa.accept_18_17_8_2_1_2622 17 62 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 146 2 8 31 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 146 2 7 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 146 (accept_3_2 13 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  146 2 6 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 146 2 5 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 146 (Polychromatic418967fa.accept_15_9_2_11_1_2391 9 62 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 146 2 4 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 146 (accept_3_2 7 62 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 146 2 3 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 146 2 2 31 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 146
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 146 2 1 31 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 146 (accept_3_2 1 62 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 146 (allA_of_3_0 61 61 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 146 (allA_succ_of_accept 59 60 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 146 2 29 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 60 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 146 2 28 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 146 (accept_3_2 55 60 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 146 2 27 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 146 2 26 30 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 146 2 25 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 146 (accept_3_2 49 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  146 2 24 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 146 2 23 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 60 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 146 2 22 30 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 146 (accept_3_2 43 60 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 146 2 21 30 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 146 2 20 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 146 2 19 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 146 (accept_3_2 37 60 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 146 2 18 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 60 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 146 2 17 30 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 146
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 146 2 16 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 146 (accept_3_2 31 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  146 2 15 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 146 (Polychromatic418967fa.accept_19_10_3_13_1_6284 29 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 146 2 14 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 60 146 (Polychromatic418967fa.accept_18_9_6_2_1_2619 27 60 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 146 2 13 30 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 146 (accept_3_2 25 60 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 146 2 12 30 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 60 146 2 11 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 60 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 60 146 2 10 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 60 146 (accept_3_2 19 60 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60 146 2 9 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 60 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 60 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 60 146 2 8 30 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 60 146
  (Polychromatic418967fa.accept_16_15_12_2_1_6502 15 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 60 146 2 7 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 60 146 (accept_3_2 13 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60
  146 2 6 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  60 146 (Polychromatic418967fa.accept_13_11_8_3_1_3016 11 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 60 146 2 5 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 60 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 60 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 60 146 2 4 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 60 146 (accept_3_2 7 60 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 146 2 3 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 60 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 60 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 60 146 2 2 30 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 60 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 60 146 2 1 30 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 60 146 (accept_3_2 1 60 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 60
  146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 146 (allA_succ_of_accept 58 59 146
  (accept_3_2 58 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 59 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 57 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 59 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 59 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 146 (accept_3_2 55 59 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 59 146 (Polychromatic418967fa.accept_16_6_11_2_1_6485 54 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 53 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 146 (accept_3_2 52 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 146 (Polychromatic418967fa.accept_13_11_7_3_1_894 50 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 146 (accept_3_2 49 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 146
  (Polychromatic418967fa.accept_13_8_7_3_1_430 47 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 146 (accept_3_2 46 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 146 (accept_3_2 43 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 146 (accept_3_2 40 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 146 (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 146 (accept_3_2 37 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 146 (Polychromatic418967fa.accept_13_10_7_3_1_3041 36 59
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 146
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 146 (accept_3_2 34 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 146 (accept_3_2 31 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 146 (accept_3_2 28 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 146 (accept_3_2 25 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 146 (accept_3_2 22 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 146 (accept_3_2 19 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 59 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 146 (accept_3_2 16 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 146 (Polychromatic418967fa.accept_13_1_7_3_1_1503 14 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 146 (accept_3_2 13 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 146
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 59 146 (accept_3_2 10 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  59 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 59 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 146 (accept_3_2 7 59 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 59 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 59 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 59
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 59 146 (accept_3_2 4 59 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 59 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 59 146 (accept_3_2 1 59 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 59
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 146 (allA_of_3_0 58 58 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 57 146 (allA_succ_of_accept 56 57 146
  (Polychromatic418967fa.accept_11_1_2_3_1_688 56 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 146 (accept_3_2 55 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 146 (accept_3_2 52 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 57 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 146 (accept_3_2 49 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 146 (Polychromatic418967fa.accept_13_9_5_3_1_428 48 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 146 (accept_3_2 46 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 146 (Polychromatic418967fa.accept_11_1_2_3_1_688 45 57 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 146
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 146 (accept_3_2 43 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 146 (accept_3_2 40 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 57 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 146
  (Polychromatic418967fa.accept_15_8_12_11_1_1570 38 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 146 (accept_3_2 37 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 146 (Polychromatic418967fa.accept_20_16_17_6_1_7799 36 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 146 (accept_3_2 34 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 57 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 146 (accept_3_2 31 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 146 (accept_3_2 28 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 57 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 146
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 146 (accept_3_2 25 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 146 (accept_3_2 22 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 146 (Polychromatic418967fa.accept_10_1_7_6_1_91 21 57 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 146
  (Polychromatic418967fa.accept_23_20_11_8_1_7798 20 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 146 (accept_3_2 19 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 146 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 146 (accept_3_2 16 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 57 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 146 (accept_3_2 13 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 146 (accept_3_2 10 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 57 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 146 (accept_3_2 7 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  146 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 146 (accept_3_2 4 57 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 57 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  57 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 146 (accept_3_2 1 57 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 146)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 146 (allA_succ_of_accept 55 56 146 (accept_3_2 55 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 146 2 27 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 146 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 56 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 146 2 26 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 146 (Polychromatic418967fa.accept_13_12_4_3_1_1528
  51 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 146 2 25 28 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 146 (accept_3_2 49
  56 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 146 2 24 28 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 146
  (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 146 2 23 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 146 (Polychromatic418967fa.accept_27_18_2_11_1_7797 45 56 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 146 2 22 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 146 (accept_3_2 43 56 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 146 2 21 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 146 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 56 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 146 2 20 28 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 146
  (Polychromatic418967fa.accept_19_1_18_13_1_7796 39 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 146 2 19 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 146 (accept_3_2 37 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  146 2 18 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 146 (Polychromatic418967fa.accept_11_2_1_3_1_683 35 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 146 2 17 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 146 (Polychromatic418967fa.accept_13_7_4_3_1_3064 33 56 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 146 2 16 28 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 146 (accept_3_2 31 56 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 146 2 15 28 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 146
  (Polychromatic418967fa.accept_12_5_8_2_1_309 29 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 56 146 2 14 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 56 146 (Polychromatic418967fa.accept_13_1_4_3_1_1545 27 56 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 56 146 2 13 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 56 146 (accept_3_2 25 56 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 56 146 2 12 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 56 146 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 56 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 146 2 11 28 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 146
  (Polychromatic418967fa.accept_20_1_16_6_1_4715 21 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 56 146 2 10 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 56 146 (accept_3_2 19 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56
  146 2 9 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  56 146 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 56 146 2 8 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 56 146 (Polychromatic418967fa.accept_17_15_5_10_1_5145 15 56 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 146 2 7 28 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 146 (accept_3_2 13 56 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 56 146 2 6 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 56 146 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 56 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 146 2 5 28 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 146
  (Polychromatic418967fa.accept_19_9_18_13_1_4931 9 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 56 146 2 4 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 56 146 (accept_3_2 7 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 146
  2 3 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56
  146 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 56 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 146 2 2 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 146 (Polychromatic418967fa.accept_22_3_12_14_1_7795 3 56 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 146 2 1 28 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 146 (accept_3_2 1 56 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 146)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 146 (allA_of_3_0 55
  55 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 146 (allA_succ_of_accept 53 54 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 146 2 26 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 146 (Polychromatic418967fa.accept_11_7_10_3_1_633 51 54 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 146 2 25 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 146 (accept_3_2 49 54 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 146 2 24 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 146 (Polychromatic418967fa.accept_15_2_9_11_1_1551 47 54 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 146 2 23 27 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 146
  (Polychromatic418967fa.accept_10_5_4_6_1_319 45 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 146 2 22 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 146 (accept_3_2 43 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  146 2 21 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 146 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 146 2 20 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 54 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 146 2 19 27 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 146 (accept_3_2 37 54 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 146 2 18 27 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 146
  (Polychromatic418967fa.accept_10_5_4_6_1_319 35 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 146 2 17 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 54 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 146 2 16 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 146 (accept_3_2 31 54 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 146 2 15 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 54 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 146 2 14 27 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 146
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 146 2 13 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 146 (accept_3_2 25 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  146 2 12 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 146 (Polychromatic418967fa.accept_13_10_2_3_1_3025 23 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 146 2 11 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 54 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 146 2 10 27 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 146 (accept_3_2 19 54 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 146 2 9 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 146 (Polychromatic418967fa.accept_15_2_9_11_1_1551
  17 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 146 2 8 27 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 146 2 7 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 146 (accept_3_2 13 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  146 2 6 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 146 2 5 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 54 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 146 2 4 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 146 (accept_3_2 7 54 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 146 2 3 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 146 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 54 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 146 2 2 27 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 146
  (Polychromatic418967fa.accept_12_3_6_2_1_747 3 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 146 2 1 27 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 146 (accept_3_2 1 54 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  146)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 146 (allA_succ_of_accept 52 53 146 (accept_3_2
  52 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 51 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 53 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 146 (accept_3_2 49 53 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 47
  53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 146 (accept_3_2 46 53
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 146 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 53 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 53 146 (accept_3_2 43 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  53 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 53 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 146 (accept_3_2 40 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 53 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 146 (accept_3_2 37 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 146 (Polychromatic418967fa.accept_19_17_15_13_1_7794 36 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 146 (accept_3_2 34 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 146 (accept_3_2 31 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 146 (Polychromatic418967fa.accept_10_9_3_6_1_686 29 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 146 (accept_3_2 28 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 53 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 146
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 146 (accept_3_2 25 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 146 (accept_3_2 22 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 146 (accept_3_2 19 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 146 (Polychromatic418967fa.accept_10_8_3_6_1_685 18 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 146 (accept_3_2 16 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 53 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 146 (accept_3_2 13 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 146 (accept_3_2 10 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 146
  (Polychromatic418967fa.accept_10_8_3_6_1_685 8 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 146 (accept_3_2 7 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  146 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 53 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 146 (accept_3_2 4 53 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 53 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  53 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 146 (accept_3_2 1 53 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 146)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 146 (allA_of_3_0 52 52 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 146
  (allA_succ_of_accept 50 51 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 51 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 146 (accept_3_2 49 51 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 146 (accept_3_2 46 51
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 146 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 51 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 51 146 (accept_3_2 43 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  51 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 42 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 51 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 146 (accept_3_2 40 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 51 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 51 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 51 146 (accept_3_2 37 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  51 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 51 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 146 (accept_3_2 34 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 51 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 51 146
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 51 146 (accept_3_2 31 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  51 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 51 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 146 (accept_3_2 28 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 146 (Polychromatic418967fa.accept_10_7_1_6_1_673 27 51 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 51 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 51 146 (accept_3_2 25 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  51 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 51 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 51 146 (accept_3_2 22 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 51 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 51 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 51 146
  (Polychromatic418967fa.accept_15_5_6_11_1_854 20 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 51 146 (accept_3_2 19 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  51 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 51 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 51 146 (accept_3_2 16 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 51 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 51 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 51 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 51 146 (accept_3_2 13 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  51 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 51 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 51 146 (accept_3_2 10 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 51 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 51 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 51 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 51 146 (accept_3_2 7 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 51
  146 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 51 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 51 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 51 146 (accept_3_2 4 51 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 51 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 51 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 51 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 2
  51 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 146 (accept_3_2 1 51 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 51 146)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 50 146 (allA_succ_of_accept 49 50 146 (accept_3_2 49 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 50 146 2 24 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 50 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 50 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 50 146 2 23 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 50 146 (Polychromatic418967fa.accept_20_5_10_6_1_6166
  45 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 146 2 22 25 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 146 (accept_3_2 43
  50 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 146 2 21 25 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 146
  (Polychromatic418967fa.accept_11_8_6_3_1_661 41 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 50 146 2 20 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 50 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 39 50 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 50 146 2 19 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 50 146 (accept_3_2 37 50 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50 146 2 18 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 50 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 50 146 2 17 25 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 50 146
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 50 146 2 16 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 50 146 (accept_3_2 31 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50
  146 2 15 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  50 146 (Polychromatic418967fa.accept_18_11_14_2_1_5058 29 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 50 146 2 14 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 50 146 (Polychromatic418967fa.accept_13_1_11_3_1_901 27 50 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 146 2 13 25 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 146 (accept_3_2 25 50 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 146 2 12 25 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 146
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 50 146 2 11 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 50 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 50 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 50 146 2 10 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 50 146 (accept_3_2 19 50 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50 146 2 9 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 50 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 50 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 50 146 2 8 25 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 50 146
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 50 146 2 7 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 50 146 (accept_3_2 13 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50
  146 2 6 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  50 146 (Polychromatic418967fa.accept_18_11_14_2_1_5058 11 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 50 146 2 5 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 50 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 50 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 50 146 2 4 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 50 146 (accept_3_2 7 50 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 146 2 3 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 50 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 50 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 50 146 2 2 25 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 50 146
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 50 146 2 1 25 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 50 146 (accept_3_2 1 50 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 50
  146)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 146 (allA_of_3_0 49 49 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 48 146 (allA_succ_of_accept 47 48 146 (Polychromatic418967fa.accept_13_8_9_3_1_2213 47
  48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 48 146 2 23 24 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 48 146
  (Polychromatic418967fa.accept_13_6_9_3_1_915 45 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 48 146 2 22 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 48 146 (accept_3_2 43 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48
  146 2 21 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  48 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 48 146 2 20 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 48 146 (Polychromatic418967fa.accept_17_5_14_10_1_2831 39 48 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 48 146 2 19 24 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 48 146 (accept_3_2 37 48 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48 146 2 18 24 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 48 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 48 146 2 17 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 48 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 146 2 16 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 146 (accept_3_2 31 48 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 146 2 15 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 146 (Polychromatic418967fa.accept_11_7_4_3_1_302 29 48 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 146 2 14 24 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 146
  (Polychromatic418967fa.accept_25_2_23_21_1_7793 27 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 146 2 13 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 146 (accept_3_2 25 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48
  146 2 12 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  48 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 48 146 2 11 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 48 146 (Polychromatic418967fa.accept_13_8_9_3_1_2213 21 48 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 146 2 10 24 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 146 (accept_3_2 19 48 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 146 2 9 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 146 (Polychromatic418967fa.accept_9_8_3_2_1_417 17
  48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 146 2 8 24 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 146
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 146 2 7 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 146 (accept_3_2 13 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48
  146 2 6 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  48 146 (Polychromatic418967fa.accept_21_11_6_20_1_4589 11 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 146 2 5 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 146 (Polychromatic418967fa.accept_19_9_10_13_1_2291 9 48 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 146 2 4 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 146 (accept_3_2 7 48 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 146 2 3 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 48 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 146 2 2 24 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 146
  (Polychromatic418967fa.accept_10_3_8_6_1_326 3 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 146 2 1 24 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 146 (accept_3_2 1 48 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  146)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 146 (allA_succ_of_accept 46 47 146 (accept_3_2 46 47
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 146 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 146
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 146 (accept_3_2 43 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 146 (Polychromatic418967fa.accept_19_4_9_13_1_7792 42 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 146 (accept_3_2 40 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 146
  (Polychromatic418967fa.accept_22_16_3_14_1_7791 38 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 146 (accept_3_2 37 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 146 (Polychromatic418967fa.accept_13_9_8_3_1_3045 35 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 146 (accept_3_2 34 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 47 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 146 (accept_3_2 31 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 146 (Polychromatic418967fa.accept_23_7_1_8_1_7790 30 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 146 (accept_3_2 28 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 146
  (Polychromatic418967fa.accept_17_9_13_10_1_1825 26 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 146 (accept_3_2 25 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 146 (Polychromatic418967fa.accept_13_11_8_3_1_3016 24 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 146 (Polychromatic418967fa.accept_10_3_7_6_1_659 23 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 146 (accept_3_2 22 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 47 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 146
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 146 (accept_3_2 19 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 146 (accept_3_2 16 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 146
  (Polychromatic418967fa.accept_17_14_13_10_1_3936 14 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 47 146 (accept_3_2 13 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 47 146 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 47 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 47 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 47 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 146 (accept_3_2 10 47 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 47
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 146 (accept_3_2 7 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  146 (Polychromatic418967fa.accept_15_6_2_11_1_325 6 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 146 (accept_3_2 4 47 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 146
  (Polychromatic418967fa.accept_21_2_5_20_1_7789 2 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 146 (accept_3_2 1 47 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  146))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 146 (allA_of_3_0 46 46 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 146 (allA_succ_of_accept 44 45 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 45
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 146 (accept_3_2 43 45 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 146 (Polychromatic418967fa.accept_12_6_9_2_1_311
  42 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 45 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 45 146 (accept_3_2 40 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  45 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 45 146 (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 45 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 146 (accept_3_2 37 45 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 146 (Polychromatic418967fa.accept_13_10_6_3_1_1515 36 45
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 45 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 45 146 (accept_3_2 34 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  45 146 (Polychromatic418967fa.accept_21_12_3_20_1_4567 33 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 45 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 45 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 45 146 (accept_3_2 31 45 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 45 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 45 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 45 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 45 146 (accept_3_2 28 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  45 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 45 146 (Polychromatic418967fa.accept_25_1_20_21_1_7788 26 45 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 45 146 (accept_3_2 25 45 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 45 146 (Polychromatic418967fa.accept_10_4_5_6_1_651 24 45 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 45 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 45 146 (accept_3_2 22 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  45 146 (Polychromatic418967fa.accept_10_1_5_6_1_649 21 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 45 146 (Polychromatic418967fa.accept_17_3_11_10_1_7787 20 45 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 45 146 (accept_3_2 19 45 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 45 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 45 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 45 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 45 146 (accept_3_2 16 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  45 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 45 146 (Polychromatic418967fa.accept_10_4_5_6_1_651 14 45 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 45 146 (accept_3_2 13 45 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 45 146 (Polychromatic418967fa.accept_20_12_5_6_1_6205 12 45 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 45 146
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 45 146 (accept_3_2 10 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  45 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 45 146 (Polychromatic418967fa.accept_22_8_1_14_1_7786 8 45 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 45 146 (accept_3_2 7 45 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 45 146 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 45 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 45 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 146 (accept_3_2 4 45 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 45 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 45
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 45 146 (accept_3_2 1 45 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45
  146))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44 146 (allA_succ_of_accept 43 44 146 (accept_3_2 43 44
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 44 146 2 21 22 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 44 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 44 146 2 20 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 44 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 44 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 146 2 19 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 146 (accept_3_2 37 44 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 146 2 18 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 146 (Polychromatic418967fa.accept_10_5_4_6_1_319 35 44 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 146 2 17 22 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 146
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 146 2 16 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 146 (accept_3_2 31 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  146 2 15 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 146 2 14 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 44 146 (Polychromatic418967fa.accept_13_1_5_3_1_888 27 44 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 146 2 13 22 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 146 (accept_3_2 25 44 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 146 2 12 22 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 44 146 2 11 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 44 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 44 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 44 146 2 10 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 44 146 (accept_3_2 19 44 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44 146 2 9 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 44 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 44 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 44 146 2 8 22 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 44 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 44 146 2 7 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 44 146 (accept_3_2 13 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44
  146 2 6 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  44 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 44 146 2 5 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 44 146 (Polychromatic418967fa.accept_13_9_5_3_1_428 9 44 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 44 146 2 4 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 44 146 (accept_3_2 7 44 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 146 2 3 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 44 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 44 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 44 146 2 2 22 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 44 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 44 146 2 1 22 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 44 146 (accept_3_2 1 44 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 44
  146)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 146 (allA_of_3_0 43 43 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 42 146 (allA_succ_of_accept 41 42 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 42 146 2 20 21 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 42 146
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 42 146 2 19 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 42 146 (accept_3_2 37 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42
  146 2 18 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  42 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 42 146 2 17 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 42 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 42 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 42 146 2 16 21 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 42 146 (accept_3_2 31 42 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42 146 2 15 21 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 42 146
  (Polychromatic418967fa.accept_15_14_12_11_1_1572 29 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 42 146 2 14 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 42 146 (Polychromatic418967fa.accept_12_3_6_2_1_747 27 42 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 146 2 13 21 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 146 (accept_3_2 25 42 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 146 2 12 21 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 146 2 11 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 42 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 146 2 10 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 146 (accept_3_2 19 42 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 146 2 9 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 42 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 146 2 8 21 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 146
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 146 2 7 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 146 (accept_3_2 13 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42
  146 2 6 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  42 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 42 146 2 5 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 42 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 42 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 146 2 4 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 146 (accept_3_2 7 42 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 146 2 3 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 42 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 146 2 2 21 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 146
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 146 2 1 21 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 146 (accept_3_2 1 42 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  146)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 146 (allA_succ_of_accept 40 41 146 (accept_3_2 40 41 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 39
  41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 146
  (Polychromatic418967fa.accept_11_5_8_3_1_66 38 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 146 (accept_3_2 37 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 146 (Polychromatic418967fa.accept_13_10_2_3_1_3025 36 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 146 (accept_3_2 34 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 146
  (Polychromatic418967fa.accept_10_2_1_6_1_634 32 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 146 (accept_3_2 31 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 146 (Polychromatic418967fa.accept_19_10_3_13_1_6284 29 41 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 146 (accept_3_2 28 41 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 41 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 146
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 146 (accept_3_2 25 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 146 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 146 (accept_3_2 22 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 146 (accept_3_2 19 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 146 (Polychromatic418967fa.accept_13_5_2_3_1_1526 18 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 146 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 146 (accept_3_2 16 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 41 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 146
  (Polychromatic418967fa.accept_13_1_2_3_1_911 14 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 146 (accept_3_2 13 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 146 (accept_3_2 10 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 146
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 146 (accept_3_2 7 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  146 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 146 (Polychromatic418967fa.accept_10_5_1_6_1_672 5 41 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 146 (accept_3_2 4 41 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 41 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 2
  41 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 146 (accept_3_2 1 41 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 146))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 146
  (allA_of_3_0 40 40 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 146 (allA_succ_of_accept 38 39 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 146 (accept_3_2 37 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 146 (Polychromatic418967fa.accept_15_6_9_11_1_858 36 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 146 (accept_3_2 34 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 39 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 146 (accept_3_2 31 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 146 (accept_3_2 28 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 146 (Polychromatic418967fa.accept_16_11_7_2_1_4185 27 39 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 146
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 146 (accept_3_2 25 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 146 (accept_3_2 22 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 39 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 146
  (Polychromatic418967fa.accept_11_9_6_3_1_1668 20 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 146 (accept_3_2 19 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 146 (accept_3_2 16 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 146 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 39 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 146 (accept_3_2 13 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 146 (accept_3_2 10 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 39 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 146 (accept_3_2 7 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  146 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 39 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 146 (accept_3_2 4 39 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 39 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  39 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 146 (accept_3_2 1 39 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 146))))))))))))))))))))))))))))))))))))))) (allB_succ 38 146
  (allA_succ_of_accept 37 38 146 (accept_3_2 37 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  146 2 18 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 146 (Polychromatic418967fa.accept_13_9_12_3_1_907 35 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 146 2 17 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 146 (Polychromatic418967fa.accept_10_3_8_6_1_326 33 38 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 146 2 16 19 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 146 (accept_3_2 31 38 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 146 2 15 19 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 146
  (Polychromatic418967fa.accept_21_8_17_20_1_3142 29 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 146 2 14 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 146 (Polychromatic418967fa.accept_15_12_8_11_1_4383 27 38 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 146 2 13 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 146 (accept_3_2 25 38 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 146 2 12 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 38 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 146 2 11 19 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 146
  (Polychromatic418967fa.accept_23_21_15_8_1_7785 21 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 146 2 10 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 146 (accept_3_2 19 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  146 2 9 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 146 (Polychromatic418967fa.accept_13_4_12_3_1_2999 17 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 146 2 8 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 146 (Polychromatic418967fa.accept_13_2_12_3_1_415 15 38 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 146 2 7 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 146 (accept_3_2 13 38 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 146 2 6 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 38 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 146 2 5 19 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 146 2 4 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 146 (accept_3_2 7 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 146
  2 3 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  146 (Polychromatic418967fa.accept_15_5_8_11_1_2350 5 38 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 38 146 2 2 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 38 146 (Polychromatic418967fa.accept_10_3_8_6_1_326 3 38 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 146 2 1 19 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 146 (accept_3_2 1 38 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 38 146)))))))))))))))))))))))))))))))))))))) (allB_succ 37 146 (allA_of_3_0 37 37 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 36 146 (allA_succ_of_accept 35 36 146
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 146 2 17 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 36 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 146 2 16 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 146 (accept_3_2 31 36 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 36 146 2 15 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 36 146 (Polychromatic418967fa.accept_17_12_2_10_1_2862 29 36
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 146 2 14 18 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 146
  (Polychromatic418967fa.accept_20_7_16_6_1_7784 27 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 146 2 13 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 146 (accept_3_2 25 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  146 2 12 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 146 2 11 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 146 (Polychromatic418967fa.accept_14_7_8_6_1_1164 21 36 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 146 2 10 18 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 146 (accept_3_2 19 36 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 146 2 9 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 146 (Polychromatic418967fa.accept_15_2_6_11_1_1587
  17 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 146 2 8 18 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 146
  (Polychromatic418967fa.accept_13_2_10_3_1_1538 15 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 146 2 7 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 146 (accept_3_2 13 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  146 2 6 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 146 (Polychromatic418967fa.accept_13_11_10_3_1_3020 11 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 146 2 5 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 36 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 146 2 4 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 146 (accept_3_2 7 36 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 146 2 3 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 36 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 146 2 2 18 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 146
  (Polychromatic418967fa.accept_15_3_6_11_1_855 3 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 146 2 1 18 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 146 (accept_3_2 1 36 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  146)))))))))))))))))))))))))))))))))))) (allB_succ 35 146 (allA_succ_of_accept 34 35 146 (accept_3_2 34 35 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 146 (accept_3_2 31 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 146 (accept_3_2 28 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 146
  (Polychromatic418967fa.accept_17_9_1_10_1_2859 26 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 146 (accept_3_2 25 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 146 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 146 (accept_3_2 22 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 35 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 146
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 146 (accept_3_2 19 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 146 (Polychromatic418967fa.accept_13_5_9_3_1_870 18 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 146 (accept_3_2 16 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 146 (accept_3_2 13 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 146 (Polychromatic418967fa.accept_10_1_5_6_1_649 11 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 146 (accept_3_2 10 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 35 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 146
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 146 (accept_3_2 7 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  146 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 35 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 146 (accept_3_2 4 35 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 146 (Polychromatic418967fa.accept_13_2_9_3_1_2212 2
  35 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 146 (accept_3_2 1 35 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 146))))))))))))))))))))))))))))))))))) (allB_succ 34 146
  (allA_of_3_0 34 34 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 146 (allA_succ_of_accept 32 33 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 146 (accept_3_2 31 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 146 (accept_3_2 28 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 33 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 146 (accept_3_2 25 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 146 (Polychromatic418967fa.accept_13_11_7_3_1_894 24 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 146 (accept_3_2 22 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 33 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 146
  (Polychromatic418967fa.accept_19_1_14_13_1_6294 20 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 146 (accept_3_2 19 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 146 (accept_3_2 16 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 33 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 146 (accept_3_2 13 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 146 (accept_3_2 10 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 146 (Polychromatic418967fa.accept_10_9_3_6_1_686 9 33 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 146
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 146 (accept_3_2 7 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  146 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 146 (accept_3_2 4 33 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 33 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 146 (Polychromatic418967fa.accept_22_2_11_14_1_7783
  2 33 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 146 (accept_3_2 1 33
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 146))))))))))))))))))))))))))))))))) (allB_succ 32 146
  (allA_succ_of_accept 31 32 146 (accept_3_2 31 32 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  146 2 15 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 146 (Polychromatic418967fa.accept_11_7_10_3_1_633 29 32 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 146 2 14 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 32 146 (Polychromatic418967fa.accept_13_1_6_3_1_1547 27 32 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 146 2 13 16 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 146 (accept_3_2 25 32 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 146 2 12 16 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 32 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 32 146 2 11 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 32 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 32 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 32 146 2 10 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 32 146 (accept_3_2 19 32 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32 146 2 9 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 32 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 32 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 32 146 2 8 16 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 32 146
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 32 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 32 146 2 7 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 32 146 (accept_3_2 13 32 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32
  146 2 6 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  32 146 (Polychromatic418967fa.accept_10_1_2_6_1_638 11 32 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 32 146 2 5 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 32 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 32 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 32 146 2 4 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 32 146 (accept_3_2 7 32 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 146 2 3 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 32 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 32 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 32 146 2 2 16 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 32 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 32 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 32 146 2 1 16 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 32 146 (accept_3_2 1 32 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 32
  146)))))))))))))))))))))))))))))))) (allB_succ 31 146 (allA_of_3_0 31 31 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 30 146 (allA_succ_of_accept 29 30 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 30 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 30 146 2 14 15 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 30 146
  (Polychromatic418967fa.accept_11_5_8_3_1_66 27 30 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 30 146 2 13 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 30 146 (accept_3_2 25 30 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30
  146 2 12 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  30 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 30 146 2 11 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 30 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 30 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 30 146 2 10 15 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 30 146 (accept_3_2 19 30 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30 146 2 9 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 30 146 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  30 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 30 146 2 8 15 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 30 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 30 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 30 146 2 7 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 30 146 (accept_3_2 13 30 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30
  146 2 6 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  30 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 30 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 30 146 2 5 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 30 146 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 30 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 30 146 2 4 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 30 146 (accept_3_2 7 30 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 146 2 3 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 30 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 30 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 30 146 2 2 15 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 30 146
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 30 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 30 146 2 1 15 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 30 146 (accept_3_2 1 30 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 30
  146)))))))))))))))))))))))))))))) (allB_succ 29 146 (allA_succ_of_accept 28 29 146 (accept_3_2 28 29 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 29 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 29 146
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 29 146 (accept_3_2 25 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  29 146 (Polychromatic418967fa.accept_19_5_10_13_1_4883 24 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 29 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 29 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 29 146 (accept_3_2 22 29 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 29 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 29 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 29 146 (accept_3_2 19 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  29 146 (Polychromatic418967fa.accept_15_3_14_11_1_1579 18 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 29 146 (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 29 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 29 146 (accept_3_2 16 29 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 29 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 29 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 29 146
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 29 146 (accept_3_2 13 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  29 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 29 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 29 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 29 146 (accept_3_2 10 29 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 29 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 29 146
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 29 146 (accept_3_2 7 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 29
  146 (Polychromatic418967fa.accept_17_6_12_10_1_7781 6 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 29 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 29 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 29 146 (accept_3_2 4 29 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 29 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 29 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 29 146
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 29 146 (accept_3_2 1 29 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 29
  146))))))))))))))))))))))))))))) (allB_succ 28 146 (allA_of_3_0 28 28 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ 27 146 (allA_succ_of_accept 26 27 146 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 27 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 146 (accept_3_2 25 27 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 146 (Polychromatic418967fa.accept_13_11_1_3_1_910 24 27 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 27 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 27 146 (accept_3_2 22 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  27 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 27 146 (Polychromatic418967fa.accept_13_7_1_3_1_1523 20 27 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 146 (accept_3_2 19 27 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 27 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 27 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 27 146 (accept_3_2 16 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  27 146 (Polychromatic418967fa.accept_13_2_1_3_1_419 15 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 27 146 (Polychromatic418967fa.accept_15_14_12_11_1_1572 14 27 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 27 146 (accept_3_2 13 27 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 27 146 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 27
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 146
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 27 146 (accept_3_2 10 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  27 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 27 146 (Polychromatic418967fa.accept_11_8_5_3_1_694 8 27 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 27 146 (accept_3_2 7 27 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 27 146 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 27 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 27 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 27
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 146 (accept_3_2 4 27 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 146 (Polychromatic418967fa.accept_10_3_7_6_1_659 3
  27 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 146
  (Polychromatic418967fa.accept_13_2_1_3_1_419 2 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 146 (accept_3_2 1 27 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  146))))))))))))))))))))))))))) (allB_succ 26 146 (allA_succ_of_accept 25 26 146 (accept_3_2 25 26 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 146 2 12 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 23
  26 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 26 146 2 11 13 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 26 146
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 26 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 26 146 2 10 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 26 146 (accept_3_2 19 26 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26
  146 2 9 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  26 146 (Polychromatic418967fa.accept_18_17_8_2_1_2622 17 26 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 26 146 2 8 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 26 146 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 26 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 146 2 7 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 146 (accept_3_2 13 26 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 146 2 6 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 26 146 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 26 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 146 2 5 13 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 146
  (Polychromatic418967fa.accept_19_9_7_13_1_7780 9 26 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 146 2 4 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 146 (accept_3_2 7 26 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 146
  2 3 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  146 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 146 2 2 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 26 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 146 2 1 13 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 146 (accept_3_2 1 26 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 146)))))))))))))))))))))))))) (allB_succ 25 146 (allA_of_3_0 25 25 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 146 (allA_succ_of_accept 23 24 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 24
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 146 2 11 12 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 146
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 146 2 10 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 146 (accept_3_2 19 24 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  146 2 9 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 146 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 146 2 8 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 146 (Polychromatic418967fa.accept_10_5_4_6_1_319 15 24 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 146 2 7 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 146 (accept_3_2 13 24 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 146 2 6 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 146 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 24 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 146 2 5 12 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 146
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 24 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 146 2 4 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 146 (accept_3_2 7 24 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 146
  2 3 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  146 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 146 2 2 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 146 2 1 12 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 146 (accept_3_2 1 24 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 146)))))))))))))))))))))))) (allB_succ 23 146 (allA_succ_of_accept 22 23 146 (accept_3_2 22
  23 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 23 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 23 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 146 (accept_3_2 19 23 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 23 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  23 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 23 146 (accept_3_2 16 23
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 23 146 (Polychromatic418967fa.accept_6_3_5_2_1_12
  15 23 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 23 146
  (Polychromatic418967fa.accept_19_14_4_13_1_7779 14 23 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 23 146 (accept_3_2 13 23 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  23 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 23 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 23 146 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 23 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 23 146 (accept_3_2 10 23 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 23 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 23 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 23 146
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 23 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 23 146 (accept_3_2 7 23 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 23
  146 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 23 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 23 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 23 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 23 146 (accept_3_2 4 23 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 23 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 23 146 (Polychromatic418967fa.accept_11_2_1_3_1_683 2
  23 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 146 (accept_3_2 1 23 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 23 146))))))))))))))))))))))) (allB_succ 22 146 (allA_of_3_0 22 22
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 21 146 (allA_succ_of_accept 20 21 146
  (Polychromatic418967fa.accept_13_7_8_3_1_1533 20 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 21 146 (accept_3_2 19 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  21 146 (Polychromatic418967fa.accept_11_7_10_3_1_633 18 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 21 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 146 (accept_3_2 16 21 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 21 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 21 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 146
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 21 146 (accept_3_2 13 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  21 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 12 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 21 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 21 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 146 (accept_3_2 10 21 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 21 146 (Polychromatic418967fa.accept_13_9_8_3_1_3045 9 21 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 146
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 21 146 (accept_3_2 7 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21
  146 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 21 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 21 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 21 146 (accept_3_2 4 21 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 21 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 21 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 21 146 (Polychromatic418967fa.accept_10_2_1_6_1_634 2
  21 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 146 (accept_3_2 1 21 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 21 146))))))))))))))))))))) (allB_succ 20 146 (allA_succ_of_accept
  19 20 146 (accept_3_2 19 20 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 146 2 9 10 73
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 146
  (Polychromatic418967fa.accept_11_6_9_3_1_1103 17 20 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 146 2 8 10 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 146 (Polychromatic418967fa.accept_28_15_20_6_1_7778 15 20 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 146 2 7 10 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 146 (accept_3_2 13 20 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 146 2 6 10 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 146 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 20 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 146 2 5 10 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 146 (Polychromatic418967fa.accept_13_9_7_3_1_1531 9
  20 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 146 2 4 10 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 146 (accept_3_2 7 20
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 146 2 3 10 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 146
  (Polychromatic418967fa.accept_12_5_8_2_1_309 5 20 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 146 2 2 10 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 146 (Polychromatic418967fa.accept_23_3_20_8_1_7777 3 20 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 146 2 1 10 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 146 (accept_3_2 1 20 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 146)))))))))))))))))))) (allB_succ 19 146 (allA_of_3_0 19 19 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 146 (allA_succ_of_accept 17 18 146 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 18 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 146 2 8 9 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 146
  (Polychromatic418967fa.accept_11_4_7_3_1_289 15 18 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 146 2 7 9 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 146 (accept_3_2 13 18 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  146 2 6 9 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 146 (Polychromatic418967fa.accept_13_11_5_3_1_889 11 18 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 146 2 5 9 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 146 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 18 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 146 2 4 9 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 146 (accept_3_2 7 18 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 146 2 3 9 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 146 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 18 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 146 2 2 9 73 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 146
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 18 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 146 2 1 9 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 146 (accept_3_2 1 18 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  146)))))))))))))))))) (allB_succ 17 146 (allA_succ_of_accept 16 17 146 (accept_3_2 16 17 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 17 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 146
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 146 (accept_3_2 13 17 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 17 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 17 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 146 (accept_3_2 10 17 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 146
  (Polychromatic418967fa.accept_11_8_6_3_1_661 8 17 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 146 (accept_3_2 7 17 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  146 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 146 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 17 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 146 (accept_3_2 4 17 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 17 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 17
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 146 (accept_3_2 1 17 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 146))))))))))))))))) (allB_succ 16 146 (allA_of_3_0 16 16 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 146 (allA_succ_of_accept 14 15 146
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 15 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 146 (accept_3_2 13 15 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 15 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 146 (accept_3_2 10 15 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 15 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 146
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 15 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 146 (accept_3_2 7 15 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  146 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 15 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 15 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 146 (accept_3_2 4 15 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 146 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 15 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 146 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  15 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 146 (accept_3_2 1 15 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 146))))))))))))))) (allB_succ 14 146 (allA_succ_of_accept 13 14
  146 (accept_3_2 13 14 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 146 2 6 7 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 146
  (Polychromatic418967fa.accept_13_11_1_3_1_910 11 14 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 146 2 5 7 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 146 (Polychromatic418967fa.accept_20_9_14_6_1_320 9 14 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 146 2 4 7 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 146 (accept_3_2 7 14 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 146 2 3 7 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 146 (Polychromatic418967fa.accept_10_5_4_6_1_319 5 14 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 146 2 2 7 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 146 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 14
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 146 2 1 7 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 146 (accept_3_2 1 14
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 146)))))))))))))) (allB_succ 13 146 (allA_of_3_0 13 13 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 146 (allA_succ_of_accept 11 12 146
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 12 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 12 146 2 5 6 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 12 146 (Polychromatic418967fa.accept_13_9_12_3_1_907 9 12 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 146 2 4 6 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 146 (accept_3_2 7 12 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 12 146 2 3 6 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 12 146 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 146 2 2 6 73 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 146 (Polychromatic418967fa.accept_18_3_12_2_1_2639 3
  12 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 12 146 2 1 6 73 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 12 146 (accept_3_2 1 12
  146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12 146)))))))))))) (allB_succ 11 146 (allA_succ_of_accept 10 11
  146 (accept_3_2 10 11 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 11 146
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 11 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 11 146 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 11 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 146 (accept_3_2 7 11 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 11 146 (Polychromatic418967fa.accept_16_6_11_2_1_6485 6 11 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 146 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 11
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 11 146 (accept_3_2 4 11 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11 146 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 11 146
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 11 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 11 146 (accept_3_2 1 11 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 11
  146))))))))))) (allB_succ 10 146 (allA_of_3_0 10 10 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 9 146
  (allA_succ_of_accept 8 9 146 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 9 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 146 (accept_3_2 7 9 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 9 146 (Polychromatic418967fa.accept_11_6_9_3_1_1103 6 9 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 146 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 9 146 (accept_3_2 4 9 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 9
  146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 9 146
  (Polychromatic418967fa.accept_13_2_9_3_1_2212 2 9 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 9 146 (accept_3_2 1 9 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 9 146)))))))))
  (allB_succ 8 146 (allA_succ_of_accept 7 8 146 (accept_3_2 7 8 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 8 146 2 3 4 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 8 146 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 8 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 146 2 2 4 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 146 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 8 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 8 146 2 1 4 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 8 146 (accept_3_2 1 8 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 8 146)))))))) (allB_succ 7 146 (allA_of_3_0 7 7 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 6 146 (allA_succ_of_accept 5 6 146 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 6 146 2 2 3 73 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 6 146
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 6 146 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 6 146 2 1 3 73 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 6 146 (accept_3_2 1 6 146 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 6 146))))))
  (allB_succ 5 146 (allA_succ_of_accept 4 5 146 (accept_3_2 4 5 146 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 5 146 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 5 146 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 146 (Polychromatic418967fa.accept_13_2_5_3_1_406 2 5 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 5 146 (accept_3_2 1 5 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 5 146))))) (allB_succ 4 146 (allA_of_3_0 4 4 146 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 3 146 (allA_succ_of_accept 2 3 146 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 3 146
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 3 146 (accept_3_2 1 3 146 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 3 146))) (allB_succ 2 146 (allA_succ_of_accept 1 2 146 (accept_3_2 1 2 146
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 2 146)) (allB_two
  146))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


