-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch164
-- name    : Polychromatic418967fa_Branch164
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:17:51.197797+00:00
-- url     : https://prove2.me/theorems/ec9bafab-eae8-42b4-8855-9d671dcba52c
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

def Polychromatic418967fa.branch_164 : allB 164 164 :=
  allB_succ' 2 163 164 (Eq.refl Bool.true) (allA_of_3_0 2 163 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  162 164 (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 164 2 1 81 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 164 (accept_3_2 1 162 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 162 164))) (allB_succ' 4 161 164 (Eq.refl Bool.true) (allA_succ_of_accept 3 161 164
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 161 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 161 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 161 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 164 (accept_3_2 1 161 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 161 164)))) (allB_succ' 5 160 164 (Eq.refl Bool.true) (allA_of_3_0 5 160 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 159 164 (Eq.refl Bool.true) (allA_succ_of_accept 5 159 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 164 (accept_3_2 4 159 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 159 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 159 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 164 (accept_3_2 1 159 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 164)))))) (allB_succ' 7 158 164 (Eq.refl Bool.true) (allA_succ_of_gcd 6 158 164 2 3
  79 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 158 164
  (Polychromatic418967fa.accept_11_5_4_10_1_524 5 158 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 158 164 2 2 79 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 158 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 158 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 164 2 1 79 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 164 (accept_3_2 1 158 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 158 164))))))) (allB_succ' 8 157 164 (Eq.refl Bool.true) (allA_of_3_0 8 157 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 156 164 (Eq.refl Bool.true) (allA_succ_of_gcd 8 156 164 4 2 39 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 164
  (accept_3_2 7 156 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 164 2 3 78 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 156 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 156 164 4 1 39 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 156 164 (Polychromatic418967fa.accept_16_3_12_4_1_170 3 156 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 164 2 1 78 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 164 (accept_3_2 1 156 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 156 164))))))))) (allB_succ' 10 155 164 (Eq.refl Bool.true) (allA_succ_of_accept 9 155 164
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 164 (Polychromatic418967fa.accept_15_8_5_14_1_986 8 155 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 164 (accept_3_2 7 155 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 164 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 155 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5
  155 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 164 (accept_3_2 4 155
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 164 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 155 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 155 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 164 (accept_3_2 1 155 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  164)))))))))) (allB_succ' 11 154 164 (Eq.refl Bool.true) (allA_of_3_0 11 154 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 153 164 (Eq.refl Bool.true) (allA_succ_of_accept 11 153 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 164 (accept_3_2 10 153 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 153 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 164 (Polychromatic418967fa.accept_16_8_9_4_1_630 8 153 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 164 (accept_3_2 7 153 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 153 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 164 (accept_3_2 4 153 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 164 (Polychromatic418967fa.accept_14_3_13_10_1_761 3 153 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 153 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 164 (accept_3_2 1 153 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 153 164)))))))))))) (allB_succ' 13 152 164 (Eq.refl Bool.true) (allA_succ_of_gcd 12 152
  164 4 3 38 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  152 164 (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 152 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 152 164 2 5 76 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 152 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 152 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 164 4 2 38 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 164 (accept_3_2 7 152 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152 164 2 3 76 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 152 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 164 4 1 38 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 152 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 152 164 2 1 76 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 152 164 (accept_3_2 1 152 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  164))))))))))))) (allB_succ' 14 151 164 (Eq.refl Bool.true) (allA_of_3_0 14 151 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 150 164 (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 164 2 7 75 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 164 (accept_3_2 13 150 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 164 2 6 75 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 164
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 150 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 164 2 5 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 150 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 150 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 164 2 4 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 164 (accept_3_2 7 150 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 150 164 2 3 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 150 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 150 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 164 2 2 75 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3
  150 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 164 2 1 75 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 164 (accept_3_2 1
  150 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 164))))))))))))))) (allB_succ' 16 149 164 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 149 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 164 (Polychromatic418967fa.accept_12_2_5_8_1_159
  14 149 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 164 (accept_3_2 13
  149 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 149 164 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 149 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 164 (accept_3_2 10 149 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 149 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 8
  149 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 164 (accept_3_2 7 149
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 164
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 149 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 149 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 164 (accept_3_2 4 149 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 149 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  149 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 164 (accept_3_2 1 149
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149 164)))))))))))))))) (allB_succ' 17 148 164 (Eq.refl
  Bool.true) (allA_of_3_0 17 148 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 147 164 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 164 (accept_3_2 16 147 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 147 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 147 164 (Polychromatic418967fa.accept_9_5_3_2_1_171
  14 147 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 164 (accept_3_2 13
  147 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 164
  (Polychromatic418967fa.accept_10_2_7_4_1_967 12 147 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 147 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 164 (accept_3_2 10 147 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 147 164 (Polychromatic418967fa.accept_13_9_4_8_1_1752 9 147 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 147 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  147 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 164 (accept_3_2 7 147
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 147 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 164 (accept_3_2 4 147 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 147 164 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 147 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 147 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  147 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 164 (accept_3_2 1 147
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 164)))))))))))))))))) (allB_succ' 19 146 164 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 146 164 2 9 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 146 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 164 2 8 73 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 164
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 146 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 164 2 7 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 146 164 (accept_3_2 13 146 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  146 164 2 6 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 146 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 146 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 146 164 2 5 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 146 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 146 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 164 2 4 73 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 164 (accept_3_2 7 146 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146 164 2 3 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 146 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 146 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 164 2 2 73 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 164
  (Polychromatic418967fa.accept_14_3_6_10_1_752 3 146 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 146 164 2 1 73 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 146 164 (accept_3_2 1 146 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  164))))))))))))))))))) (allB_succ' 20 145 164 (Eq.refl Bool.true) (allA_of_3_0 20 145 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 144 164 (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 164 4 5 36 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 164 (accept_3_2 19 144 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 164 2 9 72 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 164
  (Polychromatic418967fa.accept_26_17_14_8_1_9114 17 144 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 144 164 4 4 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 144 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 144 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 164 2 7 72 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 164 (accept_3_2 13 144 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 164 4 3 36 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 164
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 144 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 164 2 5 72 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 164 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 144 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 164 4 2 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 164 (accept_3_2 7 144 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 144 164 2 3 72 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 144 164 (Polychromatic418967fa.accept_13_5_1_8_1_1115 5 144 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 164 4 1 36 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 164 (Polychromatic418967fa.accept_19_3_11_12_1_9102
  3 144 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 164 2 1 72 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 164 (accept_3_2 1
  144 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 164))))))))))))))))))))) (allB_succ' 22 143 164
  (Eq.refl Bool.true) (allA_succ_of_accept 21 143 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 143 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 164
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 164 (accept_3_2 19 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 164 (Polychromatic418967fa.accept_17_1_7_11_1_2892 18 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 164 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 143 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 164 (accept_3_2 16 143 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 164 (accept_3_2 13 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 143 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 164 (accept_3_2 10 143 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 164
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 8 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 164 (accept_3_2 7 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 143 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 164 (accept_3_2 4 143 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 164 (accept_3_2 1 143 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  164)))))))))))))))))))))) (allB_succ' 23 142 164 (Eq.refl Bool.true) (allA_of_3_0 23 142 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 24 141 164 (Eq.refl Bool.true) (allA_succ_of_accept 23 141 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 164 (accept_3_2 22 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 164 (Polychromatic418967fa.accept_15_5_6_14_1_1721 20 141 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 164 (accept_3_2 19 141 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 141 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 164 (accept_3_2 16 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 164 (Polychromatic418967fa.accept_10_5_1_4_1_1444 15 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 141 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 141 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 164 (accept_3_2 13 141 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 141 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 164 (accept_3_2 10 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 141 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 164 (accept_3_2 7 141 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 141 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 164 (accept_3_2 4 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 141 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 141 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 164 (accept_3_2 1 141 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 164)))))))))))))))))))))))) (allB_succ' 25 140 164 (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 140 164 4 6 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 140 164 (Polychromatic418967fa.accept_15_8_5_14_1_986 23 140 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 164 2 11 70 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 21
  140 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 164 4 5 35 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 164 (accept_3_2 19
  140 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 140 164 2 9 70 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 140 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 140 164 4 4 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 140 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 140 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 164 2 7 70 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 164 (accept_3_2 13 140 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 164 4 3 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 164 (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 140
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 164 2 5 70 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 164
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 140 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 164 4 2 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 164 (accept_3_2 7 140 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  164 2 3 70 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 164 (Polychromatic418967fa.accept_13_5_10_8_1_1127 5 140 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 164 4 1 35 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 140 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 140 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 164 2 1 70 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 164 (accept_3_2 1 140 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 140 164))))))))))))))))))))))))) (allB_succ' 26 139 164 (Eq.refl Bool.true)
  (allA_of_3_0 26 139 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 138 164 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 138 164 2 13 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 164 (accept_3_2 25 138 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 164 2 12 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 138 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 164 2 11 69 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 138 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 164 2 10 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 164 (accept_3_2 19 138 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 164 2 9 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 138 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 164 2 8 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  138 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 138 164 2 7 69 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 164 (accept_3_2 13
  138 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 164 2 6 69 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 164
  (Polychromatic418967fa.accept_15_11_3_14_1_971 11 138 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 138 164 2 5 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 138 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 138 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 138 164 2 4 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 164 (accept_3_2 7 138 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 138 164 2 3 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 138 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 164 2 2 69 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 138 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  138 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 164 2 1 69 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 164 (accept_3_2 1
  138 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 164))))))))))))))))))))))))))) (allB_succ' 28 137 164
  (Eq.refl Bool.true) (allA_succ_of_accept 27 137 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 137 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 164
  (Polychromatic418967fa.accept_11_4_5_10_1_926 26 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 164 (accept_3_2 25 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 164 (Polychromatic418967fa.accept_16_8_9_4_1_630 24 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 164 (Polychromatic418967fa.accept_10_3_7_4_1_584 23 137 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 164 (accept_3_2 22 137 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 164 (accept_3_2 19 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 164 (Polychromatic418967fa.accept_15_3_2_14_1_1713 18 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 164 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 137 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 164 (accept_3_2 16 137 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 137 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 164
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 164 (accept_3_2 13 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 164 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 137 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 164 (accept_3_2 10 137 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 164 (accept_3_2 7 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 137 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 164 (accept_3_2 4 137 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 164
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 164 (accept_3_2 1 137 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  164)))))))))))))))))))))))))))) (allB_succ' 29 136 164 (Eq.refl Bool.true) (allA_of_3_0 29 136 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 135 164 (Eq.refl Bool.true) (allA_succ_of_accept 29 135 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 164 (accept_3_2 28 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 135 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 164 (accept_3_2 25 135 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 164 (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 135 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 164 (accept_3_2 22 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 164 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 135 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 164 (accept_3_2 19 135 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 164 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 135 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 164 (accept_3_2 16 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 164 (Polychromatic418967fa.accept_13_1_5_8_1_207 14 135 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 164 (accept_3_2 13 135 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 135 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 164 (accept_3_2 10 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 164 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 135 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 164 (accept_3_2 7 135 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 135 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 164 (accept_3_2 4 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 135 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 164 (Polychromatic418967fa.accept_20_2_15_4_1_7575 2 135 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 164 (accept_3_2 1 135 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135 164)))))))))))))))))))))))))))))) (allB_succ' 31 134 164 (Eq.refl
  Bool.true) (allA_succ_of_gcd 30 134 164 2 15 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 134 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 134 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 164 2 14 67 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 164
  (Polychromatic418967fa.accept_16_11_6_4_1_2228 27 134 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 164 2 13 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 164 (accept_3_2 25 134 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 164 2 12 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 134 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 164 2 11 67 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 134 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 164 2 10 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 164 (accept_3_2 19 134 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 164 2 9 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 134 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 164 2 8 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 15
  134 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 164 2 7 67 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 164 (accept_3_2 13
  134 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 164 2 6 67 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 134 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 164 2 5 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 134 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 164 2 4 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 164 (accept_3_2 7 134 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 164 2 3 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 134 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 164 2 2 67 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 3
  134 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 164 2 1 67 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 164 (accept_3_2 1
  134 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 164))))))))))))))))))))))))))))))) (allB_succ' 32 133
  164 (Eq.refl Bool.true) (allA_of_3_0 32 133 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 132 164
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 164 4 8 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 132 164 (accept_3_2 31 132 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 164 2 15 66 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 164 (Polychromatic418967fa.accept_17_12_13_11_1_2910 29 132 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 164 4 7 33 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 164
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 132 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 132 164 2 13 66 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 132 164 (accept_3_2 25 132 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 164 4 6 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 132 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 164 2 11 66 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 21
  132 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 132 164 4 5 33 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 164 (accept_3_2 19
  132 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 164 2 9 66 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 132 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 132 164 4 4 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 132 164 (Polychromatic418967fa.accept_17_15_13_11_1_4031 15 132 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 132 164 2 7 66 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 164 (accept_3_2 13 132 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 164 4 3 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11
  132 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 164 2 5 66 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 132 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 164 4 2 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 164 (accept_3_2 7 132 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132
  164 2 3 66 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 164 4 1 33 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 164 2 1 66 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 164 (accept_3_2 1 132 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 132 164))))))))))))))))))))))))))))))))) (allB_succ' 34 131 164 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 131 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 164 (Polychromatic418967fa.accept_13_6_1_8_1_1116 32 131
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 164 (accept_3_2 31 131
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 131 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 164 (accept_3_2 28 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 131 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 164 (Polychromatic418967fa.accept_9_8_5_2_1_422
  26 131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 164 (accept_3_2 25
  131 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 164
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 131 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 164 (accept_3_2 22 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 131 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 164 (Polychromatic418967fa.accept_13_7_1_8_1_1778
  20 131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 164 (accept_3_2 19
  131 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 164
  (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 131 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 164 (accept_3_2 16 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 131 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 164 (Polychromatic418967fa.accept_12_2_11_8_1_504
  14 131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 164 (accept_3_2 13
  131 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 131 164 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 164 (accept_3_2 10 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 131 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 8
  131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 164 (accept_3_2 7 131
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 164
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 131 164 (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 164 (accept_3_2 4 131 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 131 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 2
  131 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 164 (accept_3_2 1 131
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131 164)))))))))))))))))))))))))))))))))) (allB_succ' 35 130
  164 (Eq.refl Bool.true) (allA_of_3_0 35 130 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 129 164
  (Eq.refl Bool.true) (allA_succ_of_accept 35 129 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 164 (accept_3_2 34 129 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 129 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 164 (accept_3_2 31 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 164 (accept_3_2 28 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 164 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 129 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 164
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 164 (accept_3_2 25 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 164 (accept_3_2 22 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 129 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 164
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 164 (accept_3_2 19 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 164 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 164 (accept_3_2 16 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 129 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 164 (accept_3_2 13 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 164 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 164 (accept_3_2 10 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 164 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 129 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 164
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 164 (accept_3_2 7 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 164 (accept_3_2 4 129 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 164 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 129 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 164
  (Polychromatic418967fa.accept_20_2_9_4_1_4539 2 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 164 (accept_3_2 1 129 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  164)))))))))))))))))))))))))))))))))))) (allB_succ' 37 128 164 (Eq.refl Bool.true) (allA_succ_of_gcd 36 128 164 4 9 32
  41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 128 164
  (Polychromatic418967fa.accept_13_9_11_8_1_195 35 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 128 164 2 17 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 128 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 128 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 164 4 8 32 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 164 (accept_3_2 31 128 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 164 2 15 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 29
  128 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 164 4 7 32 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 164
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 164 2 13 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 164 (accept_3_2 25 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 164 4 6 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 128 164 (Polychromatic418967fa.accept_13_10_11_8_1_1770 23 128 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 164 2 11 64 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 164
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 164 4 5 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 164 (accept_3_2 19 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  128 164 2 9 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 128 164 (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 128 164 4 4 32 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 128 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 128 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 164 2 7 64 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 164 (accept_3_2 13 128 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 164 4 3 32 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 164
  (Polychromatic418967fa.accept_21_11_2_17_1_2975 11 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 128 164 2 5 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 128 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 128 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 164 4 2 32 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 164 (accept_3_2 7 128 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 164 2 3 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 128 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 164 4 1 32 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 164
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 164 2 1 64 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 164 (accept_3_2 1 128 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  164))))))))))))))))))))))))))))))))))))) (allB_succ' 38 127 164 (Eq.refl Bool.true) (allA_of_3_0 38 127 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 126 164 (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 164 2 19 63 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 164
  (accept_3_2 37 126 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 164 2 18 63 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 126 164
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 126 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 164 2 17 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 126 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 126 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 126 164 2 16 63 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 164 (accept_3_2 31 126 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 164 2 15 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 164 (Polychromatic418967fa.accept_13_3_9_8_1_4202
  29 126 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 164 2 14 63 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 164 2 13 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 164 (accept_3_2 25 126 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 164 2 12 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 164 (Polychromatic418967fa.accept_15_8_6_14_1_975 23 126 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 164 2 11 63 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 126 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 164 2 10 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 164 (accept_3_2 19 126 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 164 2 9 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 164 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 126 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 164 2 8 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 15
  126 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 126 164 2 7 63 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 164 (accept_3_2 13
  126 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 164 2 6 63 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 164
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 11 126 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 164 2 5 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 126 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 126 164 2 4 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 164 (accept_3_2 7 126 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 126 164 2 3 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 126 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 126 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 164 2 2 63 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 126 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  126 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 164 2 1 63 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 164 (accept_3_2 1
  126 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126 164))))))))))))))))))))))))))))))))))))))) (allB_succ'
  40 125 164 (Eq.refl Bool.true) (allA_succ_of_accept 39 125 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 164
  (Polychromatic418967fa.accept_11_5_4_10_1_524 38 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 164 (accept_3_2 37 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 164 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 164 (Polychromatic418967fa.accept_20_15_5_4_1_4566 35 125 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 164 (accept_3_2 34 125 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 164 (accept_3_2 31 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 164 (Polychromatic418967fa.accept_10_9_5_4_1_966 29 125 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 164 (accept_3_2 28 125 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 164
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 164 (accept_3_2 25 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 125 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 164 (accept_3_2 22 125 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 164
  (Polychromatic418967fa.accept_19_1_11_12_1_6112 20 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 125 164 (accept_3_2 19 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 125 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 125 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 125 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 164 (accept_3_2 16 125 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 164 (accept_3_2 13 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 125 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 164 (accept_3_2 10 125 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 164
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 164 (accept_3_2 7 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 125 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 164 (accept_3_2 4 125 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 164 (accept_3_2 1 125 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  164)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 124 164 (Eq.refl Bool.true) (allA_of_3_0 41 124 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 123 164 (Eq.refl Bool.true) (allA_succ_of_gcd 41 123 164 41 1
  3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 40 123 164
  (accept_3_2 40 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 123 164
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 123 164 (Polychromatic418967fa.accept_16_6_11_4_1_635 38 123 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 164 (accept_3_2 37 123 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 123 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35
  123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 164 (accept_3_2 34
  123 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 123 164
  (Polychromatic418967fa.accept_19_14_9_12_1_9113 33 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 164 (accept_3_2 31 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 123 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 164 (accept_3_2 28 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 164 (accept_3_2 25 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 164 (Polychromatic418967fa.accept_13_11_6_8_1_1121 24 123 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 164 (accept_3_2 22 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 164 (accept_3_2 19 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 123 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 164 (accept_3_2 16 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 164 (accept_3_2 13 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 123 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 164 (accept_3_2 10 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 164 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 164 (accept_3_2 7 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 123 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 164 (accept_3_2 4 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 123 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 164 (Polychromatic418967fa.accept_13_2_6_8_1_1092 2 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 164 (accept_3_2 1 123 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123 164)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 122 164 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 122 164 2 21 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 122 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 122 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 164 2 20 61 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 164 2 19 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 164 (accept_3_2 37 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 164 2 18 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 122 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 164 2 17 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 164
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 164 2 16 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 164 (accept_3_2 31 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 164 2 15 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 122 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 164 2 14 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 164
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 164 2 13 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 164 (accept_3_2 25 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 164 2 12 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 122 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 164 2 11 61 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 164 2 10 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 164 (accept_3_2 19 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 164 2 9 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 122 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 164 2 8 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  122 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 164 2 7 61 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 164 (accept_3_2 13
  122 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 164 2 6 61 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 164
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 122 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 164 2 5 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 164 (Polychromatic418967fa.accept_11_9_1_10_1_920 9 122 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 164 2 4 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 164 (accept_3_2 7 122 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 164 2 3 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 122 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 164 2 2 61 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  122 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 164 2 1 61 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 164 (accept_3_2 1
  122 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122 164)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 121 164 (Eq.refl Bool.true) (allA_of_3_0 44 121 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 120 164 (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 164 4 11 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 164 (accept_3_2 43 120 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 164 2 21 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 41
  120 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 164 4 10 30 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 120 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 120 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 120 164 2 19 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 120 164 (accept_3_2 37 120 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 164 4 9 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 120 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 164 2 17 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 120 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 33
  120 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 120 164 4 8 30 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 164 (accept_3_2 31
  120 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 164 2 15 60 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 164
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 29 120 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 120 164 4 7 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 120 164 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 120 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 120 164 2 13 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 164 (accept_3_2 25 120 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 164 4 6 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 164 2 11 60 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 120 164
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 21 120 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 120 164 4 5 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 164 (accept_3_2 19 120 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  120 164 2 9 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 120 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 120 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 120 164 4 4 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 120 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 120 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 120 164 2 7 60 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 164 (accept_3_2 13 120 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 164 4 3 30 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 120 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 164 2 5 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 120 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 120 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 120 164 4 2 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 164 (accept_3_2 7 120 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 120 164 2 3 60 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 120 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 120 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 164 4 1 30 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 120 164 (Polychromatic418967fa.accept_16_3_8_4_1_3279 3
  120 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 120 164 2 1 60 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 164 (accept_3_2 1
  120 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120 164)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 119 164 (Eq.refl Bool.true) (allA_succ_of_accept 45 119 164 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 164
  (Polychromatic418967fa.accept_16_12_7_4_1_687 44 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 164 (accept_3_2 43 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 164 (Polychromatic418967fa.accept_19_4_5_12_1_3441 42 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 164 (Polychromatic418967fa.accept_11_8_9_10_1_503 41 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 164 (accept_3_2 40 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 119 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 164
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 164 (accept_3_2 37 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 164 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 119 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 164 (accept_3_2 34 119 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 164
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 32 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 164 (accept_3_2 31 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 164 (Polychromatic418967fa.accept_11_8_9_10_1_503 30 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 164 (Polychromatic418967fa.accept_16_13_7_4_1_3248 29 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 164 (accept_3_2 28 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 119 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 164 (accept_3_2 25 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 164 (Polychromatic418967fa.accept_16_8_7_4_1_2217 24 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 164 (Polychromatic418967fa.accept_10_3_9_4_1_960 23 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 164 (accept_3_2 22 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 119 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 164
  (Polychromatic418967fa.accept_13_7_2_8_1_1746 20 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 164 (accept_3_2 19 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 164 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 164 (Polychromatic418967fa.accept_14_3_7_10_1_2146 17 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 164 (accept_3_2 16 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 119 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 164 (accept_3_2 13 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 164 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 119 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 164 (accept_3_2 10 119 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 164
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 164 (accept_3_2 7 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 164 (Polychromatic418967fa.accept_13_6_2_8_1_1782 6 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 164 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 119 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 164 (accept_3_2 4 119 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 119 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 164 (accept_3_2 1 119 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  164)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 118 164 (Eq.refl Bool.true) (allA_of_3_0 47 118 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 117 164 (Eq.refl Bool.true) (allA_succ_of_accept 47 117 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 117 164 (accept_3_2 46 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 117 164 (Polychromatic418967fa.accept_19_7_3_12_1_4787 45 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 117 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 117 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 164 (accept_3_2 43 117 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 117 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 117 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 164 (accept_3_2 40 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 117 164 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 117 164 (Polychromatic418967fa.accept_16_6_5_4_1_4330 38 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 164 (accept_3_2 37 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 117 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 117 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 117 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 117 164 (accept_3_2 34 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 117 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 117 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 164 (accept_3_2 31 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 117 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 117 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 117 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 164 (accept_3_2 28 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 117 164 (Polychromatic418967fa.accept_20_7_17_4_1_3239 27 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 117 164 (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 164 (accept_3_2 25 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 117 164 (Polychromatic418967fa.accept_15_9_12_14_1_963 24 117
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 117 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 164 (accept_3_2 22 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 117 164 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 117 164 (Polychromatic418967fa.accept_23_20_2_3_1_9112 20 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 164 (accept_3_2 19 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 117 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 117
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 117 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 164 (accept_3_2 16 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 117 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 117 164 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 164 (accept_3_2 13 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 117 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 117
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 117 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 164 (accept_3_2 10 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  117 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 117 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 117 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 164 (accept_3_2 7 117 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 117 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 117 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 117 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 164 (accept_3_2 4 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  117 164 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 117 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 117 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 117 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 164 (accept_3_2 1 117 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 117 164)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 116 164 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 116 164 4 12 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 116 164 (Polychromatic418967fa.accept_19_9_2_12_1_6243 47 116 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 164 2 23 58 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 164
  (Polychromatic418967fa.accept_10_5_6_4_1_64 45 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 164 4 11 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 164 (accept_3_2 43 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 164 2 21 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 116 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 164 4 10 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 164 2 19 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 164 (accept_3_2 37 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 164 4 9 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 116 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 164 2 17 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  116 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 164 4 8 29 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 164 (accept_3_2 31
  116 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 164 2 15 58 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 164 4 7 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 116 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 164 2 13 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 164 (accept_3_2 25 116 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 164 4 6 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 116 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 164 2 11 58 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 164 4 5 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 164 (accept_3_2 19 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 164 2 9 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 116 164 (Polychromatic418967fa.accept_13_4_12_8_1_197 17 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 116 164 4 4 29 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 116 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 116 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 164 2 7 58 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 164 (accept_3_2 13 116 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 164 4 3 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 164
  (Polychromatic418967fa.accept_25_11_16_14_1_9111 11 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 164 2 5 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 164 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 116 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 164 4 2 29 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 164 (accept_3_2 7 116 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 164 2 3 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 116 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 164 4 1 29 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 164 2 1 58 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 164 (accept_3_2 1 116 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  164))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 115 164 (Eq.refl Bool.true) (allA_of_3_0 50 115
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 51 114 164 (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 164 2
  25 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114
  164 (accept_3_2 49 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 164 2 24 57 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 164 2 23 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 114 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 45 114 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 114 164 2 22 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 164 (accept_3_2 43 114 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 114 164 2 21 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 164 2 20 57 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 114 164
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 114 164 2 19 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 164 (accept_3_2 37 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 164 2 18 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 114 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 114 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 164 2 17 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 114 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 114 164 2 16 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 114 164 (accept_3_2 31 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 164 2 15 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 114 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 164 2 14 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 114 164
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 114 164 2 13 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 114 164 (accept_3_2 25 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 164 2 12 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 114 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 114 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 164 2 11 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 114 164
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 114 164 2 10 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 114 164 (accept_3_2 19 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 164 2 9 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 114 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 164 2 8 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 114 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15
  114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 114 164 2 7 57 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 164 (accept_3_2 13
  114 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 164 2 6 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 164
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 114 164 2 5 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 114 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 114 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 114 164 2 4 57 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 164 (accept_3_2 7 114 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 164 2 3 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 114 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 164 2 2 57 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 114 164
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 114 164 2 1 57 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 114 164 (accept_3_2 1 114 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  164))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 113 164 (Eq.refl Bool.true) (allA_succ_of_accept
  51 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 113 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 164 (accept_3_2 49 113 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 113 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 164 (accept_3_2 46 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 113 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 164 (accept_3_2 43 113 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 113 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 164
  (Polychromatic418967fa.accept_21_20_8_17_1_7437 41 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 113 164 (accept_3_2 40 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 113
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 164 (accept_3_2 37 113
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 164
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 36 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 113 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 164 (accept_3_2 34 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 113 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 164 (Polychromatic418967fa.accept_7_4_1_3_1_277
  32 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 164 (accept_3_2 31
  113 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 113 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 164 (accept_3_2 28 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 113 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 164 (Polychromatic418967fa.accept_7_5_1_3_1_103
  26 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 164 (accept_3_2 25
  113 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 164
  (Polychromatic418967fa.accept_9_6_5_2_1_421 24 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 113 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 164 (accept_3_2 22 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 113 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 164 (Polychromatic418967fa.accept_13_7_9_8_1_188
  20 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 164 (accept_3_2 19
  113 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 113 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 164 (accept_3_2 16 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 113 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 164 (Polychromatic418967fa.accept_12_2_5_8_1_159
  14 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 164 (accept_3_2 13
  113 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 113 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 164 (accept_3_2 10 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 113 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 164 (accept_3_2 7 113
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 164
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 113 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 164 (accept_3_2 4 113 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 113 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 113 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  113 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 164 (accept_3_2 1 113
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113 164))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 53 112 164 (Eq.refl Bool.true) (allA_of_3_0 53 112 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 54 111 164 (Eq.refl Bool.true) (allA_succ_of_accept 53 111 164 (Polychromatic418967fa.accept_6_5_3_2_1_68
  53 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 164 (accept_3_2 52
  111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 111 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 111 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 111 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 164 (accept_3_2 49 111 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 111 164 (Polychromatic418967fa.accept_13_9_7_8_1_1122 48 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 111 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 164 (accept_3_2 46 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 111 164 (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 111 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 164 (accept_3_2 43 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 111 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 111 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 164 (accept_3_2 40 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 111 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 111 164 (Polychromatic418967fa.accept_13_12_7_8_1_1104 38 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 164 (accept_3_2 37 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 111 164 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 111
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 111 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 164 (accept_3_2 34 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 111 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 111 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 164 (accept_3_2 31 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 111 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 111 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 164 (accept_3_2 28 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 111 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 111 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 164 (accept_3_2 25 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 111 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 111 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 164 (accept_3_2 22 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 111 164 (Polychromatic418967fa.accept_16_5_15_4_1_9099 21 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 111 164 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 164 (accept_3_2 19 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 111 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 111 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 111 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 164 (accept_3_2 16 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 111 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 111 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 164 (accept_3_2 13 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 111 164 (Polychromatic418967fa.accept_13_12_7_8_1_1104 12 111 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 111 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 164 (accept_3_2 10 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  111 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 111 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 164 (accept_3_2 7 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 111 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 111 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 111 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 164 (accept_3_2 4 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  111 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 111 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 111 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 164 (accept_3_2 1 111 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 111 164)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 110 164
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 110 164 2 27 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 110 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 110 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 164 2 26 55 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 164 2 25 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 164 (accept_3_2 49 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 164 2 24 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 110 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 164 2 23 55 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 164
  (Polychromatic418967fa.accept_19_7_15_12_1_4800 45 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 110 164 2 22 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 110 164 (accept_3_2 43 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 164 2 21 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 110 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 164 2 20 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 164
  (Polychromatic418967fa.accept_15_9_5_14_1_973 39 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 164 2 19 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 164 (accept_3_2 37 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 164 2 18 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 110 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 164 2 17 55 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 164
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 33 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 110 164 2 16 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 110 164 (accept_3_2 31 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 164 2 15 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 110 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 164 2 14 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 164
  (Polychromatic418967fa.accept_13_1_6_8_1_208 27 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 164 2 13 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 164 (accept_3_2 25 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 164 2 12 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 110 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 164 2 11 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 164
  (Polychromatic418967fa.accept_15_6_5_14_1_429 21 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 164 2 10 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 164 (accept_3_2 19 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 164 2 9 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 110 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 164 2 8 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 164 2 7 55 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 164 (accept_3_2 13
  110 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 164 2 6 55 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 164
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 164 2 5 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 110 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 164 2 4 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 164 (accept_3_2 7 110 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 164 2 3 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 110 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 164 2 2 55 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 164 (Polychromatic418967fa.accept_19_3_15_12_1_9110
  3 110 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 164 2 1 55 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 164 (accept_3_2 1
  110 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 109 164 (Eq.refl Bool.true) (allA_of_3_0 56
  109 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 57 108 164 (Eq.refl Bool.true) (allA_succ_of_gcd 56 108
  164 4 14 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55
  108 164 (accept_3_2 55 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 108 164 2 27 54 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 108 164
  (Polychromatic418967fa.accept_16_5_12_4_1_4325 53 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 108 164 4 13 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 108 164 (Polychromatic418967fa.accept_13_12_4_8_1_1120 51 108 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 108 164 2 25 54 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 164 (accept_3_2 49 108 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 108 164 4 12 27 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 108 164
  (Polychromatic418967fa.accept_15_2_3_14_1_972 47 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 108 164 2 23 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 108 164 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 108 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 108 164 4 11 27 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 164 (accept_3_2 43 108 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 108 164 2 21 54 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 164
  (Polychromatic418967fa.accept_11_8_9_10_1_503 41 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 108 164 4 10 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 108 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 108 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 108 164 2 19 54 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 164 (accept_3_2 37 108 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 108 164 4 9 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 108 164 (Polychromatic418967fa.accept_13_9_4_8_1_1752
  35 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 164 2 17 54 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 108 164
  (Polychromatic418967fa.accept_16_1_12_4_1_695 33 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 108 164 4 8 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 108 164 (accept_3_2 31 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  108 164 2 15 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 108 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 164 4 7 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 108 164
  (Polychromatic418967fa.accept_16_11_12_4_1_3195 27 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 108 164 2 13 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 108 164 (accept_3_2 25 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 164 4 6 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 164 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 108 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 164 2 11 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 108 164 (Polychromatic418967fa.accept_16_5_12_4_1_4325
  21 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 108 164 4 5 27 41
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 164
  (accept_3_2 19 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 164 2 9 54 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 164
  (Polychromatic418967fa.accept_15_2_3_14_1_972 17 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 164 4 4 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 108 164 (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 108 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 108 164 2 7 54 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 164 (accept_3_2 13 108 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 164 4 3 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 164 (Polychromatic418967fa.accept_13_11_4_8_1_1098
  11 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 108 164 2 5 54 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 108 164
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 108 164 4 2 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 164 (accept_3_2 7 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108
  164 2 3 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  108 164 (Polychromatic418967fa.accept_16_5_12_4_1_4325 5 108 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 108 164 4 1 27 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 108 164 (Polychromatic418967fa.accept_16_3_12_4_1_170 3 108 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 108 164 2 1 54 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 164 (accept_3_2 1 108 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 108 164))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 107 164
  (Eq.refl Bool.true) (allA_succ_of_accept 57 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 164
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 56 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 164 (accept_3_2 55 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 164 (Polychromatic418967fa.accept_10_3_7_4_1_584 53 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 164 (accept_3_2 52 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 107 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 164 (accept_3_2 49 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 164 (accept_3_2 46 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 164
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 44 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 164 (accept_3_2 43 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 164 (accept_3_2 40 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 164 (accept_3_2 37 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 164 (Polychromatic418967fa.accept_13_9_3_8_1_573 35 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 164 (accept_3_2 34 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 107 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 164 (accept_3_2 31 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 164 (accept_3_2 28 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 164 (accept_3_2 25 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 164 (accept_3_2 22 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 164
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 164 (accept_3_2 19 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 164 (Polychromatic418967fa.accept_13_5_3_8_1_1117 18 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 164 (Polychromatic418967fa.accept_20_17_7_4_1_7671 17 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 164 (accept_3_2 16 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 107 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 164 (accept_3_2 13 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 164 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 164 (accept_3_2 10 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 107 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 164 (accept_3_2 7 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 164 (accept_3_2 4 107 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 107 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 164
  (Polychromatic418967fa.accept_10_2_7_4_1_967 2 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 164 (accept_3_2 1 107 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 106 164 (Eq.refl Bool.true) (allA_of_3_0
  59 106 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 105 164 (Eq.refl Bool.true) (allA_succ_of_accept 59
  105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 105 164 (accept_3_2 58 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 105 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 105 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 105 164 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 105
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 164 (accept_3_2 55 105
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 105 164
  (Polychromatic418967fa.accept_12_6_9_8_1_165 54 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 105 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 164 (accept_3_2 52 105 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 105 164 (Polychromatic418967fa.accept_10_1_5_4_1_276 51 105 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 105 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 105 164 (accept_3_2 49 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 105 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 164 (accept_3_2 46 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 105 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 105 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 105 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 164 (accept_3_2 43 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 105 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 164 (accept_3_2 40 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 105 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 105 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 105 164
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 164 (accept_3_2 37 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 105 164 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 164 (accept_3_2 34 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 105 164 (Polychromatic418967fa.accept_13_7_1_8_1_1778 33 105 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 105 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 105 164 (accept_3_2 31 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 105 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 164 (accept_3_2 28 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 105 164 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 105 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 105 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 164 (accept_3_2 25 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 105 164 (Polychromatic418967fa.accept_13_11_1_8_1_1776 24 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 164 (accept_3_2 22 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 105 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 105 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 105 164
  (Polychromatic418967fa.accept_13_7_1_8_1_1778 20 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 164 (accept_3_2 19 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 105 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 164 (accept_3_2 16 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 105 164 (Polychromatic418967fa.accept_20_15_5_4_1_4566 15 105 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 105 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 164 (accept_3_2 13 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 105 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 164 (accept_3_2 10 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 105 164 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 105 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 105 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 164 (accept_3_2 7 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  105 164 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 105 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 164 (accept_3_2 4 105 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 105 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 105 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 105 164
  (Polychromatic418967fa.accept_17_2_3_11_1_2919 2 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 164 (accept_3_2 1 105 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 104 164 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 104 164 4 15 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 164 (Polychromatic418967fa.accept_11_4_5_10_1_926 59 104 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 164 2 29 52 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 164 4 14 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 164 (accept_3_2 55 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 164 2 27 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 104 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 164 4 13 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 164 2 25 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 164 (accept_3_2 49 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 164 4 12 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 164 (Polychromatic418967fa.accept_16_15_8_4_1_1355 47 104 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 164 2 23 52 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 164
  (Polychromatic418967fa.accept_14_3_6_10_1_752 45 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 164 4 11 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 164 (accept_3_2 43 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 164 2 21 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 164 (Polychromatic418967fa.accept_16_9_8_4_1_1354 41 104 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 164 4 10 26 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 164 2 19 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 164 (accept_3_2 37 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 164 4 9 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 104 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 104 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 164 2 17 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 33
  104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 164 4 8 26 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 164 (accept_3_2 31
  104 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 164 2 15 52 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 164
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 29 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 104 164 4 7 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 104 164 (Polychromatic418967fa.accept_16_11_8_4_1_2234 27 104 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 104 164 2 13 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 104 164 (accept_3_2 25 104 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 104 164 4 6 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 104 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 104 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 164 2 11 52 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 164 4 5 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 104 164 (accept_3_2 19 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  104 164 2 9 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 104 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 104 164 4 4 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 104 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 104 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 164 2 7 52 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 164 (accept_3_2 13 104 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 164 4 3 26 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 164 2 5 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 104 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 164 4 2 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 164 (accept_3_2 7 104 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 164 2 3 52 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 164 (Polychromatic418967fa.accept_16_5_8_4_1_5418 5 104 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 164 4 1 26 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 3
  104 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 164 2 1 52 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 164 (accept_3_2 1
  104 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 103 164 (Eq.refl Bool.true)
  (allA_of_3_0 62 103 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 102 164 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 102 164 2 31 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 102 164 (accept_3_2 61 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 164 2 30 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 102 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 164 2 29 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 102 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 102 164 2 28 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 102 164 (accept_3_2 55 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 164 2 27 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 102 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 164 2 26 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 102 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 102 164 2 25 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 102 164 (accept_3_2 49 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 164 2 24 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 164 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 102 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 164 2 23 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 102 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 102 164 2 22 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 102 164 (accept_3_2 43 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 164 2 21 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 102 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 102 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 164 2 20 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 102 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 102 164 2 19 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 102 164 (accept_3_2 37 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 164 2 18 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 102 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 164 2 17 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 102 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 102 164 2 16 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 102 164 (accept_3_2 31 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 164 2 15 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 102 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 164 2 14 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 102 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 102 164 2 13 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 102 164 (accept_3_2 25 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 164 2 12 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 102 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 102 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 164 2 11 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 102 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 102 164 2 10 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 102 164 (accept_3_2 19 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 164 2 9 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 102 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 164 2 8 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 102 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 102 164 2 7 51 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 164 (accept_3_2 13
  102 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 164 2 6 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 164
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 102 164 2 5 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 102 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 102 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 102 164 2 4 51 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 164 (accept_3_2 7 102 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 164 2 3 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 102 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 164 2 2 51 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 102 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 102 164 2 1 51 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 102 164 (accept_3_2 1 102 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 101 164 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 101 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 62 101
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 164 (accept_3_2 61 101
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 164
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 60 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 101 164 (Polychromatic418967fa.accept_13_7_10_8_1_567 59 101 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 164 (accept_3_2 58 101 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 101 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 164
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 164 (accept_3_2 55 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 164 (Polychromatic418967fa.accept_13_2_10_8_1_1126 54 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 164 (Polychromatic418967fa.accept_18_17_11_2_1_7782 53 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 164 (accept_3_2 52 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 101 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 164
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 164 (accept_3_2 49 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 164 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 164 (Polychromatic418967fa.accept_10_7_1_4_1_1447 47 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 164 (accept_3_2 46 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 101 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 164
  (Polychromatic418967fa.accept_13_5_10_8_1_1127 44 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 164 (accept_3_2 43 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 164 (Polychromatic418967fa.accept_15_12_11_14_1_3464 42 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 41 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 164 (accept_3_2 40 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 101 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 164
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 164 (accept_3_2 37 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 164 (Polychromatic418967fa.accept_19_17_6_12_1_7757 36 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 164 (Polychromatic418967fa.accept_10_5_1_4_1_1444 35 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 164 (accept_3_2 34 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 101 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 164
  (Polychromatic418967fa.accept_17_15_16_11_1_4001 32 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 101 164 (accept_3_2 31 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 101 164 (Polychromatic418967fa.accept_13_4_10_8_1_1817 30 101 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 164 (Polychromatic418967fa.accept_17_12_16_11_1_7885 29
  101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 164 (accept_3_2 28
  101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 164
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 101 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 101 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 164 (accept_3_2 25 101 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 101 164 (Polychromatic418967fa.accept_13_11_10_8_1_1804 24 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 164
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 23 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 164 (accept_3_2 22 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 164 (Polychromatic418967fa.accept_13_7_10_8_1_567 20 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 164 (accept_3_2 19 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 164 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 101
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 164
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 164 (accept_3_2 16 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 164 (accept_3_2 13 101 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 164 (Polychromatic418967fa.accept_11_1_2_10_1_1426 12 101
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 164
  (Polychromatic418967fa.accept_13_11_10_8_1_1804 11 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 101 164 (accept_3_2 10 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 101 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 164 (Polychromatic418967fa.accept_16_8_5_4_1_674 8 101 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 164 (accept_3_2 7 101 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 164 (Polychromatic418967fa.accept_14_6_3_10_1_3905
  6 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 164
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 164 (accept_3_2 4 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 101 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 101 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 164 (accept_3_2 1 101 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101 164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65
  100 164 (Eq.refl Bool.true) (allA_of_3_0 65 100 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 99 164
  (Eq.refl Bool.true) (allA_succ_of_accept 65 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 99 164 (accept_3_2 64 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 99 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 99 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 99 164
  (Polychromatic418967fa.accept_19_5_4_12_1_7773 62 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 99 164 (accept_3_2 61 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  99 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 99 164 (accept_3_2 58 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 99 164 (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 99 164
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 56 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 99 164 (accept_3_2 55 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  99 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 99 164 (accept_3_2 52 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 99 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 99 164
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 50 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 99 164 (accept_3_2 49 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  99 164 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 99 164 (accept_3_2 46 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 99 164 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 99 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 99 164 (accept_3_2 43 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  99 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 99 164 (accept_3_2 40 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 99 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 99 164
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 99 164 (accept_3_2 37 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  99 164 (Polychromatic418967fa.accept_15_6_9_14_1_3457 36 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 99 164 (accept_3_2 34 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 99 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 99 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 99 164 (accept_3_2 31 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  99 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 99 164 (accept_3_2 28 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 99 164 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 99 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 99 164 (accept_3_2 25 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  99 164 (Polychromatic418967fa.accept_16_8_3_4_1_3233 24 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 99 164 (accept_3_2 22 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 99 164 (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 99 164
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 99 164 (accept_3_2 19 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  99 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 99 164 (accept_3_2 16 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 99 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 99 164
  (Polychromatic418967fa.accept_20_14_19_4_1_7534 14 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 99 164 (accept_3_2 13 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  99 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 99 164 (accept_3_2 10 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 99 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 99 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 99 164
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 99 164 (accept_3_2 7 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 99
  164 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 99 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 99 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 99 164 (accept_3_2 4 99 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 99 164 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 99 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 99 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  99 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 99 164 (accept_3_2 1 99 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 99
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 98 164 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 98 164 2 33 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 98 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 98 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 98 164 2 32 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 98 164
  (Polychromatic418967fa.accept_17_12_13_11_1_2910 63 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 98 164 2 31 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 98 164 (accept_3_2 61 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 98 164 2 30 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 98 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 98 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 98 164 2 29 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 98 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 57
  98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 98 164 2 28 49 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 98 164 (accept_3_2 55
  98 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 98 164 2 27 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 98 164
  (Polychromatic418967fa.accept_12_5_2_8_1_172 53 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 98 164 2 26 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 98 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 98 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 98 164 2 25 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 98 164 (accept_3_2 49 98 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 98 164 2 24 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 98 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 98 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 98 164 2 23 49 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 98 164
  (Polychromatic418967fa.accept_19_7_3_12_1_4787 45 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 98 164 2 22 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 98 164 (accept_3_2 43 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 98
  164 2 21 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  98 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 98 164 2 20 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 98 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 98 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 98 164 2 19 49 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 98 164 (accept_3_2 37 98 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 98 164 2 18 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 98 164
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 98 164 2 17 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 98 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 33 98 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 98 164 2 16 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 98 164 (accept_3_2 31 98 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 98 164 2 15 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 98 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 98 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 98 164 2 14 49 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 98 164
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 27 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 98 164 2 13 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 98 164 (accept_3_2 25 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 98
  164 2 12 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  98 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 98 164 2 11 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 98 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 98 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 98 164 2 10 49 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 98 164 (accept_3_2 19 98 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 98 164 2 9 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 98 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 98 164 2 8 49 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 98 164
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 98 164 2 7 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 98 164 (accept_3_2 13 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 98
  164 2 6 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  98 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 98 164 2 5 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 98 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 98 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 98 164 2 4 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 98 164 (accept_3_2 7 98 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 98 164 2 3 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 98 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 98 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 98 164 2 2 49 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 98 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 98 164 2 1 49 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 98 164 (accept_3_2 1 98 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 98
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 97 164 (Eq.refl Bool.true)
  (allA_of_3_0 68 97 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 96 164 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 96 164 4 17 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 96 164 (accept_3_2 67 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 96
  164 2 33 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65
  96 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 64 96 164 4 16 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 63 96 164 (Polychromatic418967fa.accept_18_9_6_2_1_2619 63 96 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 96 164 2 31 48 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 96 164 (accept_3_2 61 96 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 96 164 4 15 24 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 96 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 96 164 2 29 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 96 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 96 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 96 164 4 14 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 96 164 (accept_3_2 55 96 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 96 164 2 27 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 96 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 96 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 96 164 4 13 24 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 96 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 96 164 2 25 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 96 164 (accept_3_2 49 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 96
  164 4 12 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  96 164 (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 96 164 2 23 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 96 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 96 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 96 164 4 11 24 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 96 164 (accept_3_2 43 96 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 96 164 2 21 48 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 96 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 96 164 4 10 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 96 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 96 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 96 164 2 19 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 96 164 (accept_3_2 37 96 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 96 164 4 9 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 96 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 96 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 96 164 2 17 48 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 96 164
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 33 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 96 164 4 8 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 96 164 (accept_3_2 31 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 96
  164 2 15 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  96 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 96 164 4 7 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 96 164 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 96 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 96 164 2 13 48 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 96 164 (accept_3_2 25 96 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 96 164 4 6 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 96 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 96 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 96 164 2 11 48 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 96 164
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 96 164 4 5 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 96 164 (accept_3_2 19 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 96
  164 2 9 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  96 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 96 164 4 4 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 96 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 96 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 96 164 2 7 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 96 164 (accept_3_2 13 96 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 96 164 4 3 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 96 164 (Polychromatic418967fa.accept_19_11_1_12_1_6237 11 96 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 96 164 2 5 48 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 96 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 96 164 4 2 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 96 164 (accept_3_2 7 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 96 164
  2 3 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 96
  164 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 96 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 96 164 4 1 24 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 96 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 96 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 96 164 2 1 48 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 96 164 (accept_3_2 1 96 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 96 164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 95
  164 (Eq.refl Bool.true) (allA_succ_of_accept 69 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 95 164
  (Polychromatic418967fa.accept_15_8_5_14_1_986 68 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 95 164 (accept_3_2 67 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  95 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 95 164 (Polychromatic418967fa.accept_20_5_15_4_1_7635 65 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 95 164 (accept_3_2 64 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 95 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 95 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 95 164 (accept_3_2 61 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  95 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 95 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 59 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 95 164 (accept_3_2 58 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 95 164
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 95 164 (accept_3_2 55 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  95 164 (Polychromatic418967fa.accept_15_9_5_14_1_973 54 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 95 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 95 164 (accept_3_2 52 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 95 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 95 164 (accept_3_2 49 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  95 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 95 164 (Polychromatic418967fa.accept_11_3_7_10_1_180 47 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 95 164 (accept_3_2 46 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 95 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 95 164 (accept_3_2 43 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  95 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 95 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 95 164 (accept_3_2 40 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 95 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 95 164 (accept_3_2 37 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  95 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 95 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 95 164 (accept_3_2 34 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 95 164
  (Polychromatic418967fa.accept_15_2_5_14_1_61 32 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 95 164 (accept_3_2 31 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  95 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 95 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 95 164 (accept_3_2 28 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 95 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 95 164 (accept_3_2 25 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  95 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 95 164 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 95 164 (accept_3_2 22 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 95 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 95 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 95 164 (accept_3_2 19 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  95 164 (Polychromatic418967fa.accept_17_1_10_11_1_2943 18 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 95 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 95 164 (accept_3_2 16 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 95 164
  (Polychromatic418967fa.accept_11_3_7_10_1_180 14 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 95 164 (accept_3_2 13 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  95 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 95 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 95 164 (accept_3_2 10 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 95 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 95 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 95 164 (accept_3_2 7 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 95
  164 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 95 164 (Polychromatic418967fa.accept_16_5_15_4_1_9099 5 95 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 95 164 (accept_3_2 4 95 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 95 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 95 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 95 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  95 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 95 164 (accept_3_2 1 95 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 95
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 94 164 (Eq.refl Bool.true)
  (allA_of_3_0 71 94 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 93 164 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 93 164 (accept_3_2 70 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 93 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 93 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 68
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 93 164 (accept_3_2 67 93
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 93 164
  (Polychromatic418967fa.accept_12_6_9_8_1_165 66 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 93 164 (accept_3_2 64 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 93 164 (Polychromatic418967fa.accept_18_9_3_2_1_3814 63 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 93 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 62
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 93 164 (accept_3_2 61 93
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 93 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 60 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 93 164 (accept_3_2 58 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 93 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 93 164 (Polychromatic418967fa.accept_15_11_3_14_1_971
  56 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 93 164 (accept_3_2 55
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 93 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 93 164 (accept_3_2 52 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 93 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 93 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 50
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 93 164 (accept_3_2 49 93
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 93 164
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 93 164 (accept_3_2 46 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 93 164 (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 93 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 44
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 93 164 (accept_3_2 43 93
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 93 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 42 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 93 164 (accept_3_2 40 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 93 164 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 93 164 (Polychromatic418967fa.accept_16_6_13_4_1_643
  38 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 93 164 (accept_3_2 37
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 93 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 93 164 (accept_3_2 34 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 93 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 93 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 32
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 93 164 (accept_3_2 31 93
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 93 164
  (Polychromatic418967fa.accept_12_6_9_8_1_165 30 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 93 164 (accept_3_2 28 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 93 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 93 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 26
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 93 164 (accept_3_2 25 93
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 93 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 24 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 93 164 (accept_3_2 22 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 93 164 (Polychromatic418967fa.accept_19_2_17_12_1_6097 21 93 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 93 164
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 93 164 (accept_3_2 19 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  93 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 93 164 (accept_3_2 16 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 93 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 93 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 93 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 93 164 (accept_3_2 13 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  93 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 93 164 (accept_3_2 10 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 93 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 93 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 93 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 93 164 (accept_3_2 7 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 93
  164 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 93 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 93 164 (accept_3_2 4 93 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 93 164 (Polychromatic418967fa.accept_19_3_17_12_1_6176 3 93 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 93 164 (Polychromatic418967fa.accept_15_2_3_14_1_972 2
  93 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 93 164 (accept_3_2 1 93 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 93
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 92 164 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 92 164 4 18 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 92 164 (Polychromatic418967fa.accept_11_5_4_10_1_524 71 92 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 92 164 2 35 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 92 164 (Polychromatic418967fa.accept_16_5_12_4_1_4325
  69 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 92 164 4 17 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 92 164 (accept_3_2 67
  92 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 92 164 2 33 46 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 92 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 92 164 4 16 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 92 164 (Polychromatic418967fa.accept_13_11_1_8_1_1776 63 92 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 92 164 2 31 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 92 164 (accept_3_2 61 92 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 92 164 4 15 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 92 164 (Polychromatic418967fa.accept_13_7_1_8_1_1778 59 92 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 92 164 2 29 46 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 92 164
  (Polychromatic418967fa.accept_10_7_2_4_1_569 57 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 92 164 4 14 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 92 164 (accept_3_2 55 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 92
  164 2 27 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  92 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 92 164 4 13 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 92 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 92 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 92 164 2 25 46 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 92 164 (accept_3_2 49 92 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 92 164 4 12 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 92 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 92 164 2 23 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 92 164 (Polychromatic418967fa.accept_13_6_1_8_1_1116 45 92 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 92 164 4 11 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 92 164 (accept_3_2 43 92 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 92 164 2 21 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 92 164 (Polychromatic418967fa.accept_16_9_12_4_1_3255 41 92 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 92 164 4 10 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 92 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 92 164 2 19 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 92 164 (accept_3_2 37 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 92
  164 4 9 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  92 164 (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 92 164 2 17 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 92 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 92 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 92 164 4 8 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 92 164 (accept_3_2 31 92 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 92 164 2 15 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 92 164 (Polychromatic418967fa.accept_16_13_12_4_1_4323
  29 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 92 164 4 7 23 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 92 164
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 92 164 2 13 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 92 164 (accept_3_2 25 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 92
  164 4 6 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  92 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 92 164 2 11 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 92 164 (Polychromatic418967fa.accept_16_5_12_4_1_4325 21 92 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 92 164 4 5 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 92 164 (accept_3_2 19 92 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 92 164 2 9 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 92 164 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 92 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 92 164 4 4 23 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 92 164
  (Polychromatic418967fa.accept_16_15_12_4_1_4324 15 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 92 164 2 7 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 92 164 (accept_3_2 13 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 92
  164 4 3 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  92 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 92 164 2 5 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 92 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 92 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 92 164 4 2 23 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 92 164 (accept_3_2 7 92 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 92 164 2 3 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 92 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 92 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 92 164 4 1 23 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 92 164
  (Polychromatic418967fa.accept_15_3_2_14_1_1713 3 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 92 164 2 1 46 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 92 164 (accept_3_2 1 92 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 92
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 91 164 (Eq.refl Bool.true)
  (allA_of_3_0 74 91 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 90 164 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 90 164 2 37 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 90 164 (accept_3_2 73 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 90
  164 2 36 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  90 164 (Polychromatic418967fa.accept_20_11_10_4_1_7520 71 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 90 164 2 35 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 90 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 69 90 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 90 164 2 34 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 90 164 (accept_3_2 67 90 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 90 164 2 33 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 90 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 90 164 2 32 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 90 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 90 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 90 164 2 31 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 90 164 (accept_3_2 61 90 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 90 164 2 30 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 90 164 (Polychromatic418967fa.accept_13_7_12_8_1_199 59 90 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 90 164 2 29 45 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 90 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 90 164 2 28 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 90 164 (accept_3_2 55 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 90
  164 2 27 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  90 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 90 164 2 26 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 90 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 90 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 90 164 2 25 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 90 164 (accept_3_2 49 90 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 90 164 2 24 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 90 164
  (Polychromatic418967fa.accept_19_9_14_12_1_7764 47 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 90 164 2 23 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 90 164 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 90 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 90 164 2 22 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 90 164 (accept_3_2 43 90 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 90 164 2 21 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 90 164 (Polychromatic418967fa.accept_17_7_5_11_1_2922 41 90 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 90 164 2 20 45 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 90 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 90 164 2 19 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 90 164 (accept_3_2 37 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 90
  164 2 18 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  90 164 (Polychromatic418967fa.accept_13_9_12_8_1_570 35 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 90 164 2 17 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 90 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 90 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 90 164 2 16 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 90 164 (accept_3_2 31 90 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 90 164 2 15 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 90 164
  (Polychromatic418967fa.accept_19_10_14_12_1_4795 29 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 90 164 2 14 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 90 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 90 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 90 164 2 13 45 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 90 164 (accept_3_2 25 90 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 90 164 2 12 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 90 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 90 164 2 11 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 90 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 90 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 90 164 2 10 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 90 164 (accept_3_2 19 90 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 90 164 2 9 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 90 164 (Polychromatic418967fa.accept_13_4_12_8_1_197 17 90 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 90 164 2 8 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 90 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 90 164 2 7 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 90 164 (accept_3_2 13 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 90
  164 2 6 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  90 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 90 164 2 5 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 90 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 90 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 90 164 2 4 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 90 164 (accept_3_2 7 90 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 90 164 2 3 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 90 164 (Polychromatic418967fa.accept_13_5_12_8_1_198 5 90 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 90 164 2 2 45 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 90 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 90 164 2 1 45 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 90 164 (accept_3_2 1 90 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 90
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 89 164 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 89 164 (Polychromatic418967fa.accept_12_2_5_8_1_159
  74 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 89 164 (accept_3_2 73
  89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 89 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 89 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 89 164 (accept_3_2 70 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 89 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 68
  89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 89 164 (accept_3_2 67 89
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 89 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 66 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 89 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 89 164 (accept_3_2 64 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 89 164 (Polychromatic418967fa.accept_12_2_5_8_1_159
  62 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 89 164 (accept_3_2 61
  89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 89 164
  (Polychromatic418967fa.accept_9_6_8_2_1_410 60 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 89 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 89 164 (accept_3_2 58 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 89 164 (Polychromatic418967fa.accept_13_4_11_8_1_1768
  56 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 89 164 (accept_3_2 55
  89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 89 164
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 89 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 53 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 89 164 (accept_3_2 52 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 89 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 50
  89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 89 164 (accept_3_2 49 89
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 89 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 48 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 89 164 (Polychromatic418967fa.accept_18_11_17_2_1_6349 47 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 89 164 (accept_3_2 46 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 89 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 44
  89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 89 164 (accept_3_2 43 89
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 89 164
  (Polychromatic418967fa.accept_9_6_8_2_1_410 42 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 89 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 89 164 (accept_3_2 40 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 89 164 (Polychromatic418967fa.accept_10_8_9_4_1_961
  38 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 89 164 (accept_3_2 37
  89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 89 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 89 164 (Polychromatic418967fa.accept_10_5_9_4_1_1420 35 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 89 164 (accept_3_2 34 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 89 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 32
  89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 89 164 (accept_3_2 31 89
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 89 164 (Polychromatic418967fa.accept_7_2_5_3_1_98
  30 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 89 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 89 164 (accept_3_2 28 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 89 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 26 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 89 164 (accept_3_2 25 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 89 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 89 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 89 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 89 164 (accept_3_2 22 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 89 164 (Polychromatic418967fa.accept_11_9_1_10_1_920 20 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 89 164 (accept_3_2 19 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 89 164 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 89 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 89 164
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 17 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 89 164 (accept_3_2 16 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 89 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 89 164 (accept_3_2 13 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 89 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 89 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 89 164
  (Polychromatic418967fa.accept_16_11_9_4_1_5438 11 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 89 164 (accept_3_2 10 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  89 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 89 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 89 164 (accept_3_2 7 89 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 89 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 89 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 89 164
  (Polychromatic418967fa.accept_8_5_1_4_1_628 5 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 89 164 (accept_3_2 4 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 89
  164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 89 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 89 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 89 164 (accept_3_2 1 89 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 89 164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  77 88 164 (Eq.refl Bool.true) (allA_of_3_0 77 88 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 87 164
  (Eq.refl Bool.true) (allA_succ_of_accept 77 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 87 164 (accept_3_2 76 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 87 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 75 87 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 87 164
  (Polychromatic418967fa.accept_26_22_9_8_1_9109 74 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 87 164 (accept_3_2 73 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  87 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 87 164 (accept_3_2 70 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 87 164 (Polychromatic418967fa.accept_13_4_9_8_1_1736 69 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 87 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 87 164 (accept_3_2 67 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  87 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 87 164 (accept_3_2 64 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 87 164 (Polychromatic418967fa.accept_10_3_7_4_1_584 63 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 87 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 87 164 (accept_3_2 61 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  87 164 (Polychromatic418967fa.accept_16_12_7_4_1_687 60 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 87 164 (accept_3_2 58 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 87 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 87 164
  (Polychromatic418967fa.accept_13_4_9_8_1_1736 56 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 87 164 (accept_3_2 55 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  87 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 87 164 (accept_3_2 52 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 87 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 87 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 87 164 (accept_3_2 49 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  87 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 87 164 (accept_3_2 46 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 87 164 (Polychromatic418967fa.accept_16_13_7_4_1_3248 45 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 87 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 87 164 (accept_3_2 43 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  87 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 87 164 (accept_3_2 40 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 87 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 87 164
  (Polychromatic418967fa.accept_13_12_9_8_1_2595 38 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 87 164 (accept_3_2 37 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  87 164 (Polychromatic418967fa.accept_21_15_3_17_1_9108 36 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 87 164 (accept_3_2 34 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 87 164 (Polychromatic418967fa.accept_10_3_7_4_1_584 33 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 87 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 87 164 (accept_3_2 31 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  87 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 87 164 (accept_3_2 28 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 87 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 87 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 87 164 (accept_3_2 25 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  87 164 (Polychromatic418967fa.accept_13_11_9_8_1_1125 24 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 87 164 (accept_3_2 22 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 87 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 87 164
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 87 164 (accept_3_2 19 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  87 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 87 164 (accept_3_2 16 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 87 164 (Polychromatic418967fa.accept_21_15_3_17_1_9108 15 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 87 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 87 164 (accept_3_2 13 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  87 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 87 164 (accept_3_2 10 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 87 164 (Polychromatic418967fa.accept_15_9_12_14_1_963 9 87 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 87 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 87 164 (accept_3_2 7 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 87
  164 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 87 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 87 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 87 164 (accept_3_2 4 87 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 87 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 87 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 87 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  87 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 87 164 (accept_3_2 1 87 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 87
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 86 164 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 86 164 2 39 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 86 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 86 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 86 164 2 38 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 86 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 75 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 86 164 2 37 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 86 164 (accept_3_2 73 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 86
  164 2 36 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  86 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 86 164 2 35 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 86 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 86 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 86 164 2 34 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 86 164 (accept_3_2 67 86 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 86 164 2 33 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 86 164
  (Polychromatic418967fa.accept_10_5_6_4_1_64 65 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 86 164 2 32 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 86 164 (Polychromatic418967fa.accept_11_8_9_10_1_503 63 86 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 86 164 2 31 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 86 164 (accept_3_2 61 86 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 86 164 2 30 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 86 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 86 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 86 164 2 29 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 86 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 86 164 2 28 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 86 164 (accept_3_2 55 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 86
  164 2 27 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  86 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 86 164 2 26 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 86 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 51 86 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 86 164 2 25 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 86 164 (accept_3_2 49 86 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 86 164 2 24 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 86 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 86 164 2 23 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 86 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 86 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 86 164 2 22 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 86 164 (accept_3_2 43 86 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 86 164 2 21 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 86 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 86 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 86 164 2 20 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 86 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 86 164 2 19 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 86 164 (accept_3_2 37 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 86
  164 2 18 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  86 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 86 164 2 17 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 86 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 86 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 86 164 2 16 43 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 86 164 (accept_3_2 31 86 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 86 164 2 15 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 86 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 86 164 2 14 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 86 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 86 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 86 164 2 13 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 86 164 (accept_3_2 25 86 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 86 164 2 12 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 86 164 (Polychromatic418967fa.accept_11_1_9_10_1_184 23 86 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 86 164 2 11 43 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 86 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 86 164 2 10 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 86 164 (accept_3_2 19 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 86
  164 2 9 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  86 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 86 164 2 8 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 86 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 86 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 86 164 2 7 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 86 164 (accept_3_2 13 86 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 86 164 2 6 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 86 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 86 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 86 164 2 5 43 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 86 164
  (Polychromatic418967fa.accept_19_9_10_12_1_6161 9 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 86 164 2 4 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 86 164 (accept_3_2 7 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 86 164
  2 3 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 86
  164 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 86 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 86 164 2 2 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 86 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 86 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 86 164 2 1 43 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 86 164 (accept_3_2 1 86 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 86 164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 80 85 164 (Eq.refl Bool.true) (allA_of_3_0 80 85 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  81 84 164 (Eq.refl Bool.true) (allA_succ_of_gcd 80 84 164 4 20 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 84 164 (accept_3_2 79 84 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 84 164 2 39 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 84 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 84 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 84 164 4 19 21 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 84 164
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 75 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 84 164 2 37 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 73 84 164 (accept_3_2 73 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 84
  164 4 18 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71
  84 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 70 84 164 2 35 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 69 84 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 84 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 84 164 4 17 21 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 84 164 (accept_3_2 67 84 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 84 164 2 33 42 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 84 164
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 65 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 84 164 4 16 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 84 164 (Polychromatic418967fa.accept_13_11_6_8_1_1121 63 84 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 84 164 2 31 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 84 164 (accept_3_2 61 84 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 84 164 4 15 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 84 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 84 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 84 164 2 29 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 84 164
  (Polychromatic418967fa.accept_15_12_9_14_1_2635 57 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 84 164 4 14 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 84 164 (accept_3_2 55 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 84
  164 2 27 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  84 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 84 164 4 13 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 84 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 84 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 84 164 2 25 42 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 84 164 (accept_3_2 49 84 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 84 164 4 12 21 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 84 164
  (Polychromatic418967fa.accept_11_3_7_10_1_180 47 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 84 164 2 23 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 84 164 (Polychromatic418967fa.accept_19_7_8_12_1_9107 45 84 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 84 164 4 11 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 84 164 (accept_3_2 43 84 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 84 164 2 21 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 84 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 84 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 84 164 4 10 21 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 84 164
  (Polychromatic418967fa.accept_17_5_16_11_1_3998 39 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 84 164 2 19 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 84 164 (accept_3_2 37 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 84
  164 4 9 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  84 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 84 164 2 17 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 84 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 84 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 84 164 4 8 21 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 84 164 (accept_3_2 31 84 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 84 164 2 15 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 84 164
  (Polychromatic418967fa.accept_17_12_16_11_1_7885 29 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 84 164 4 7 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 84 164 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 84 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 84 164 2 13 42 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 84 164 (accept_3_2 25 84 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 84 164 4 6 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 84 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 84 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 84 164 2 11 42 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 84 164
  (Polychromatic418967fa.accept_15_6_9_14_1_3457 21 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 84 164 4 5 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 84 164 (accept_3_2 19 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 84
  164 2 9 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  84 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 84 164 4 4 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 84 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 84 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 84 164 2 7 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 84 164 (accept_3_2 13 84 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 84 164 4 3 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 84 164 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 84 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 84 164 2 5 42 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 84 164
  (Polychromatic418967fa.accept_22_9_18_10_1_7319 9 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 84 164 4 2 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 84 164 (accept_3_2 7 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 84 164
  2 3 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 84
  164 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 84 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 84 164 4 1 21 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 84 164 (Polychromatic418967fa.accept_11_3_7_10_1_180 3 84 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 84 164 2 1 42 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 84 164 (accept_3_2 1 84 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 84 164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 82 83 164 (Eq.refl Bool.true) (allA_succ_of_accept 81 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 81
  83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 83 164
  (Polychromatic418967fa.accept_15_5_8_14_1_432 80 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 83 164 (accept_3_2 79 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  83 164 (Polychromatic418967fa.accept_23_9_14_3_1_5608 78 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 83 164 (Polychromatic418967fa.accept_10_7_3_4_1_978 77 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 83 164 (accept_3_2 76 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 83 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 74 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 83 164 (accept_3_2 73 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  83 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 72 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 83 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 71 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 83 164 (accept_3_2 70 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 83 164
  (Polychromatic418967fa.accept_13_3_5_8_1_1099 68 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 83 164 (accept_3_2 67 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  83 164 (Polychromatic418967fa.accept_13_1_5_8_1_207 66 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 83 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 83 164 (accept_3_2 64 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 83 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 83 164 (accept_3_2 61 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  83 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 83 164 (Polychromatic418967fa.accept_10_9_3_4_1_985 59 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 83 164 (accept_3_2 58 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 83 164
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 56 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 83 164 (accept_3_2 55 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  83 164 (Polychromatic418967fa.accept_15_9_8_14_1_1699 54 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 83 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 83 164 (accept_3_2 52 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 83 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 83 164 (accept_3_2 49 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  83 164 (Polychromatic418967fa.accept_22_4_17_10_1_9106 48 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 83 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 47 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 83 164 (accept_3_2 46 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 83 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 83 164 (accept_3_2 43 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  83 164 (Polychromatic418967fa.accept_13_3_5_8_1_1099 42 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 83 164 (Polychromatic418967fa.accept_19_3_7_12_1_9105 41 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 83 164 (accept_3_2 40 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 83 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 83 164
  (Polychromatic418967fa.accept_11_5_6_10_1_1432 38 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 83 164 (accept_3_2 37 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  83 164 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 83 164 (Polychromatic418967fa.accept_15_5_8_14_1_432 35 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 83 164 (accept_3_2 34 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 83 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 83 164 (accept_3_2 31 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  83 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 83 164 (Polychromatic418967fa.accept_10_9_3_4_1_985 29 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 83 164 (accept_3_2 28 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 83 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 83 164 (accept_3_2 25 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  83 164 (Polychromatic418967fa.accept_15_9_8_14_1_1699 24 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 83 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 83 164 (accept_3_2 22 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 83 164
  (Polychromatic418967fa.accept_15_5_8_14_1_432 20 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 83 164 (accept_3_2 19 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  83 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 83 164 (Polychromatic418967fa.accept_10_7_3_4_1_978 17 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 83 164 (accept_3_2 16 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 83 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 83 164 (accept_3_2 13 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  83 164 (Polychromatic418967fa.accept_13_12_5_8_1_1101 12 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 83 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 83 164 (accept_3_2 10 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 83 164
  (Polychromatic418967fa.accept_16_8_3_4_1_3233 8 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 83 164 (accept_3_2 7 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 83
  164 (Polychromatic418967fa.accept_15_6_8_14_1_4575 6 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 83 164 (Polychromatic418967fa.accept_11_5_6_10_1_1432 5 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 83 164 (accept_3_2 4 83 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 83 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 83 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 83 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 83 164 (accept_3_2 1 83 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 83
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 82 164 (allA_of_3_0
  82 82 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 81 164 (allA_succ_of_accept 80 81 164
  (Polychromatic418967fa.accept_15_5_6_14_1_1721 80 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 81 164 (accept_3_2 79 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78
  81 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 78 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 81 164 (accept_3_2 76 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 81 164 (Polychromatic418967fa.accept_10_5_1_4_1_1444 75 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 81 164
  (Polychromatic418967fa.accept_13_9_3_8_1_573 74 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 81 164 (accept_3_2 73 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72
  81 164 (Polychromatic418967fa.accept_13_7_3_8_1_1750 72 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 81 164 (accept_3_2 70 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 81 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 81 164
  (Polychromatic418967fa.accept_15_8_6_14_1_975 68 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 81 164 (accept_3_2 67 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  81 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 81 164 (accept_3_2 64 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 81 164 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 81 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 81 164 (accept_3_2 61 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  81 164 (Polychromatic418967fa.accept_11_5_4_10_1_524 60 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 81 164 (accept_3_2 58 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 81 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 81 164
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 56 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 81 164 (accept_3_2 55 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  81 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 81 164 (accept_3_2 52 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 81 164 (Polychromatic418967fa.accept_16_3_1_4_1_5426 51 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 81 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 81 164 (accept_3_2 49 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  81 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 81 164 (accept_3_2 46 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 81 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 81 164
  (Polychromatic418967fa.accept_13_5_3_8_1_1117 44 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 81 164 (accept_3_2 43 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  81 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 81 164 (accept_3_2 40 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 81 164 (Polychromatic418967fa.accept_15_9_6_14_1_2627 39 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 81 164
  (Polychromatic418967fa.accept_11_5_4_10_1_524 38 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 81 164 (accept_3_2 37 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  81 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 81 164 (accept_3_2 34 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 81 164 (Polychromatic418967fa.accept_13_7_3_8_1_1750 33 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 81 164
  (Polychromatic418967fa.accept_17_15_13_11_1_4031 32 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 81 164 (accept_3_2 31 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 81 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 81 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 81 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 81 164 (accept_3_2 28 81 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 81 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 27
  81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 81 164
  (Polychromatic418967fa.accept_19_7_5_12_1_7756 26 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 81 164 (accept_3_2 25 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  81 164 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 81 164 (accept_3_2 22 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 81 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 81 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 81 164 (accept_3_2 19 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  81 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 81 164 (accept_3_2 16 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 81 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 81 164
  (Polychromatic418967fa.accept_16_14_1_4_1_5432 14 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 81 164 (accept_3_2 13 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  81 164 (Polychromatic418967fa.accept_16_12_1_4_1_5403 12 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 81 164 (accept_3_2 10 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 81 164 (Polychromatic418967fa.accept_13_9_3_8_1_573 9 81 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 81 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 81 164 (accept_3_2 7 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 81
  164 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 81 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 81 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 81 164 (accept_3_2 4 81 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 81 164 (Polychromatic418967fa.accept_16_3_1_4_1_5426 3 81 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 81 164 (Polychromatic418967fa.accept_39_2_3_8_1_9104 2
  81 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 81 164 (accept_3_2 1 81 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 81
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 80 164
  (allA_succ_of_accept 79 80 164 (accept_3_2 79 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 80
  164 2 39 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77
  80 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 76 80 164 4 19 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 80 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 75 80 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 80 164 2 37 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 80 164 (accept_3_2 73 80 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 80 164 4 18 20 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 80 164
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 71 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 80 164 2 35 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 80 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 69 80 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 80 164 4 17 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 80 164 (accept_3_2 67 80 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 80 164 2 33 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 80 164 (Polychromatic418967fa.accept_17_14_12_11_1_4063 65 80
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 80 164 4 16 20 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 80 164
  (Polychromatic418967fa.accept_19_6_4_12_1_6193 63 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 80 164 2 31 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 80 164 (accept_3_2 61 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 80
  164 4 15 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  80 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 80 164 2 29 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 80 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 80 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 80 164 4 14 20 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 80 164 (accept_3_2 55 80 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 80 164 2 27 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 80 164
  (Polychromatic418967fa.accept_15_8_5_14_1_986 53 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 80 164 4 13 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 80 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 51 80 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 80 164 2 25 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 80 164 (accept_3_2 49 80 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 80 164 4 12 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 80 164 (Polychromatic418967fa.accept_15_2_5_14_1_61 47 80 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 80 164 2 23 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 80 164
  (Polychromatic418967fa.accept_13_6_2_8_1_1782 45 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 80 164 4 11 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 80 164 (accept_3_2 43 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 80
  164 2 21 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  80 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 80 164 4 10 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 80 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 80 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 80 164 2 19 40 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 80 164 (accept_3_2 37 80 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 80 164 4 9 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 80 164 (Polychromatic418967fa.accept_18_17_8_2_1_2622
  35 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 80 164 2 17 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 80 164
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 80 164 4 8 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 80 164 (accept_3_2 31 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 80
  164 2 15 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  80 164 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 80 164 4 7 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 80 164 (Polychromatic418967fa.accept_19_8_4_12_1_4768 27 80 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 80 164 2 13 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 80 164 (accept_3_2 25 80 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 80 164 4 6 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 80 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 80 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 80 164 2 11 40 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 80 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 80 164 4 5 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 80 164 (accept_3_2 19 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 80
  164 2 9 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  80 164 (Polychromatic418967fa.accept_15_2_5_14_1_61 17 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 80 164 4 4 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 80 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 15 80 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 80 164 2 7 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 80 164 (accept_3_2 13 80 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 80 164 4 3 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 80 164 (Polychromatic418967fa.accept_19_11_4_12_1_6106 11 80 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 80 164 2 5 40 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 80 164
  (Polychromatic418967fa.accept_15_9_5_14_1_973 9 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 80 164 4 2 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 80 164 (accept_3_2 7 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 80 164
  2 3 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 80
  164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 80 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 80 164 4 1 20 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 80 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 80 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 80 164 2 1 40 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 80 164 (accept_3_2 1 80 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 80 164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 79 164 (allA_of_3_0 79 79 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 78 164
  (allA_succ_of_accept 77 78 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 78 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 78 164 2 38 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 78 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 75
  78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 78 164 2 37 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 78 164 (accept_3_2 73
  78 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 78 164 2 36 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 78 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 71 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 78 164 2 35 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 78 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 69 78 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 78 164 2 34 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 78 164 (accept_3_2 67 78 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 78 164 2 33 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 78 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 78 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 78 164 2 32 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 78 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 78 164 2 31 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 78 164 (accept_3_2 61 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 78
  164 2 30 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  78 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 78 164 2 29 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 78 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 78 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 78 164 2 28 39 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 78 164 (accept_3_2 55 78 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 78 164 2 27 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 78 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 78 164 2 26 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 78 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 78 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 78 164 2 25 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 78 164 (accept_3_2 49 78 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 78 164 2 24 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 78 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 78 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 78 164 2 23 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 78 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 78 164 2 22 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 78 164 (accept_3_2 43 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 78
  164 2 21 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  78 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 78 164 2 20 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 78 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 78 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 78 164 2 19 39 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 78 164 (accept_3_2 37 78 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 78 164 2 18 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 78 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 35 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 78 164 2 17 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 78 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 78 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 78 164 2 16 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 78 164 (accept_3_2 31 78 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 78 164 2 15 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 78 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 78 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 78 164 2 14 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 78 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 78 164 2 13 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 78 164 (accept_3_2 25 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 78
  164 2 12 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  78 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 78 164 2 11 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 78 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 78 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 78 164 2 10 39 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 78 164 (accept_3_2 19 78 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 78 164 2 9 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 78 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 17
  78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 78 164 2 8 39 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 78 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 78 164 2 7 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 78 164 (accept_3_2 13 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 78
  164 2 6 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  78 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 78 164 2 5 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 78 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 78 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 78 164 2 4 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 78 164 (accept_3_2 7 78 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 78 164 2 3 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 78 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 78 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 78 164 2 2 39 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 78 164
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 78 164 2 1 39 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 78 164 (accept_3_2 1 78 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 78
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 77 164
  (allA_succ_of_accept 76 77 164 (accept_3_2 76 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 77 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 74 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 77 164 (accept_3_2 73 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 77 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 72 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 77 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 77 164 (accept_3_2 70 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 77 164 (Polychromatic418967fa.accept_19_11_1_12_1_6237 68 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 77 164 (accept_3_2 67 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 77 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 77 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 77 164
  (Polychromatic418967fa.accept_8_1_5_4_1_388 65 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 77 164 (accept_3_2 64 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 77 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 77 164 (accept_3_2 61 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 77 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 77 164
  (Polychromatic418967fa.accept_13_7_12_8_1_199 59 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 77 164 (accept_3_2 58 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 77 164 (Polychromatic418967fa.accept_13_4_12_8_1_197 56 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 77 164 (accept_3_2 55 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 77 164 (Polychromatic418967fa.accept_16_6_13_4_1_643 54 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 77 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 77 164 (accept_3_2 52 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 77 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 50 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 77 164 (accept_3_2 49 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 77 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 77 164
  (Polychromatic418967fa.accept_19_9_1_12_1_6234 47 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 77 164 (accept_3_2 46 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 77 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 77 164 (accept_3_2 43 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 77 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 77 164
  (Polychromatic418967fa.accept_8_1_5_4_1_388 41 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 77 164 (accept_3_2 40 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 77 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 77 164 (accept_3_2 37 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 77 164 (Polychromatic418967fa.accept_13_10_12_8_1_2550 36 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 77 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 77 164 (accept_3_2 34 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 77 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 32 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 77 164 (accept_3_2 31 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 77 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 77 164
  (Polychromatic418967fa.accept_21_8_14_17_1_2968 29 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 77 164 (accept_3_2 28 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 77 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 77 164 (accept_3_2 25 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 77 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 77 164
  (Polychromatic418967fa.accept_10_3_7_4_1_584 23 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 77 164 (accept_3_2 22 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 77 164 (Polychromatic418967fa.accept_13_7_12_8_1_199 20 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 77 164 (accept_3_2 19 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 77 164 (Polychromatic418967fa.accept_13_5_12_8_1_198 18 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 77 164
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 77 164 (accept_3_2 16 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 77 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 77 164 (accept_3_2 13 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 77 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 77 164
  (Polychromatic418967fa.accept_10_1_7_4_1_968 11 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 77 164 (accept_3_2 10 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  77 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 77 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 77 164 (accept_3_2 7 77 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 77 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 77 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 77 164
  (Polychromatic418967fa.accept_13_5_12_8_1_198 5 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 77 164 (accept_3_2 4 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 77
  164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 77 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 77 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 77 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 77 164 (accept_3_2 1 77 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 77 164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ
  76 164 (allA_of_3_0 76 76 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 75 164 (allA_succ_of_accept 74 75
  164 (Polychromatic418967fa.accept_11_8_9_10_1_503 74 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 75 164 (accept_3_2 73 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 75 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 72 75 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 75 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 75 164 (accept_3_2 70 75 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 75 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 69
  75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 75 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 68 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 75 164 (accept_3_2 67 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  75 164 (Polychromatic418967fa.accept_10_6_5_4_1_571 66 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 75 164 (accept_3_2 64 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 75 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 63 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 75 164
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 75 164 (accept_3_2 61 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  75 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 75 164 (accept_3_2 58 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 75 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 75 164
  (Polychromatic418967fa.accept_10_6_5_4_1_571 56 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 75 164 (accept_3_2 55 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  75 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 75 164 (accept_3_2 52 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 75 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 75 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 50 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 75 164 (accept_3_2 49 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  75 164 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 75 164 (accept_3_2 46 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 75 164 (Polychromatic418967fa.accept_11_1_9_10_1_184 45 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 75 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 75 164 (accept_3_2 43 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  75 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 75 164 (accept_3_2 40 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 75 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 75 164
  (Polychromatic418967fa.accept_13_12_10_8_1_3343 38 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 75 164 (accept_3_2 37 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  75 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 75 164 (accept_3_2 34 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 75 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 75 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 75 164 (accept_3_2 31 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  75 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 75 164 (accept_3_2 28 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 75 164 (Polychromatic418967fa.accept_18_9_3_2_1_3814 27 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 75 164
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 75 164 (accept_3_2 25 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  75 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 75 164 (accept_3_2 22 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 75 164 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 75 164
  (Polychromatic418967fa.accept_13_7_10_8_1_567 20 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 75 164 (accept_3_2 19 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  75 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 75 164 (accept_3_2 16 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 75 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 75 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 75 164 (accept_3_2 13 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  75 164 (Polychromatic418967fa.accept_11_1_9_10_1_184 12 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 75 164 (accept_3_2 10 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 75 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 75 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 75 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 75 164 (accept_3_2 7 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 75
  164 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 75 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 75 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 75 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 75 164 (accept_3_2 4 75 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 75 164 (Polychromatic418967fa.accept_21_3_12_17_1_7471 3 75 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 75 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 75
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 75 164 (accept_3_2 1 75 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 75
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 74 164 (allA_succ_of_accept
  73 74 164 (accept_3_2 73 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 74 164 2 36 37 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 74 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 74 164 2 35 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 74 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 74 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 74 164 2 34 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 74 164 (accept_3_2 67 74 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 74 164 2 33 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 74 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 74 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 74 164 2 32 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 74 164
  (Polychromatic418967fa.accept_13_11_9_8_1_1125 63 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 74 164 2 31 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 74 164 (accept_3_2 61 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 74
  164 2 30 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  74 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 74 164 2 29 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 74 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 74 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 74 164 2 28 37 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 74 164 (accept_3_2 55 74 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 74 164 2 27 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 74 164
  (Polychromatic418967fa.accept_11_9_8_10_1_934 53 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 74 164 2 26 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 74 164 (Polychromatic418967fa.accept_13_12_9_8_1_2595 51 74 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 74 164 2 25 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 74 164 (accept_3_2 49 74 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 74 164 2 24 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 74 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 74 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 74 164 2 23 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 74 164
  (Polychromatic418967fa.accept_27_18_20_2_1_9103 45 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 74 164 2 22 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 74 164 (accept_3_2 43 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 74
  164 2 21 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  74 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 74 164 2 20 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 74 164 (Polychromatic418967fa.accept_17_5_6_11_1_3974 39 74 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 74 164 2 19 37 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 74 164 (accept_3_2 37 74 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 74 164 2 18 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 74 164
  (Polychromatic418967fa.accept_12_11_2_8_1_511 35 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 74 164 2 17 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 74 164 (Polychromatic418967fa.accept_13_7_9_8_1_188 33 74 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 74 164 2 16 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 74 164 (accept_3_2 31 74 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 74 164 2 15 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 74 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 74 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 74 164 2 14 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 74 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 74 164 2 13 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 74 164 (accept_3_2 25 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 74
  164 2 12 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  74 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 74 164 2 11 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 74 164 (Polychromatic418967fa.accept_14_7_4_10_1_1351 21 74 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 74 164 2 10 37 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 74 164 (accept_3_2 19 74 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 74 164 2 9 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 74 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 17
  74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 74 164 2 8 37 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 74 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 74 164 2 7 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 74 164 (accept_3_2 13 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 74
  164 2 6 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  74 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 74 164 2 5 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 74 164 (Polychromatic418967fa.accept_11_9_8_10_1_934 9 74 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 74 164 2 4 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 74 164 (accept_3_2 7 74 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 74 164 2 3 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 74 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 74 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 74 164 2 2 37 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 74 164
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 74 164 2 1 37 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 74 164 (accept_3_2 1 74 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 74
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 73 164 (allA_of_3_0 73 73 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 72 164 (allA_succ_of_accept 71 72 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 72 164 2 35 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 72 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 72 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 72 164 4 17 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 72 164 (accept_3_2 67 72 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 66 72 164 2 33 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 72 164 (Polychromatic418967fa.accept_16_1_8_4_1_4334 65 72 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 72 164 4 16 18 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 72 164
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 63 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 72 164 2 31 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 61 72 164 (accept_3_2 61 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 72
  164 4 15 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59
  72 164 (Polychromatic418967fa.accept_16_11_8_4_1_2234 59 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 72 164 2 29 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 72 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 72 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 72 164 4 14 18 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 72 164 (accept_3_2 55 72 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 72 164 2 27 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 72 164
  (Polychromatic418967fa.accept_13_1_7_8_1_1796 53 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 72 164 4 13 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 72 164 (Polychromatic418967fa.accept_13_12_7_8_1_1104 51 72 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 72 164 2 25 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 72 164 (accept_3_2 49 72 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 72 164 4 12 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 72 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 72 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 72 164 2 23 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 72 164
  (Polychromatic418967fa.accept_16_13_8_4_1_3250 45 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 72 164 4 11 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 72 164 (accept_3_2 43 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 72
  164 2 21 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  72 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 72 164 4 10 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 72 164 (Polychromatic418967fa.accept_15_9_12_14_1_963 39 72 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 72 164 2 19 36 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 72 164 (accept_3_2 37 72 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 72 164 4 9 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 72 164 (Polychromatic418967fa.accept_13_9_7_8_1_1122
  35 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 72 164 2 17 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 72 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 72 164 4 8 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 72 164 (accept_3_2 31 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 72
  164 2 15 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  72 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 72 164 4 7 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 72 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 72 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 72 164 2 13 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 72 164 (accept_3_2 25 72 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 72 164 4 6 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 72 164 (Polychromatic418967fa.accept_13_10_7_8_1_1794 23 72 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 72 164 2 11 36 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 72 164
  (Polychromatic418967fa.accept_16_5_8_4_1_5418 21 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 72 164 4 5 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 72 164 (accept_3_2 19 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 72
  164 2 9 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  72 164 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 72 164 4 4 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 72 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 72 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 72 164 2 7 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 72 164 (accept_3_2 13 72 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 72 164 4 3 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 72 164 (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 72 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 72 164 2 5 36 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 72 164
  (Polychromatic418967fa.accept_13_9_7_8_1_1122 9 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 72 164 4 2 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 72 164 (accept_3_2 7 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 72 164
  2 3 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 72
  164 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 72 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 72 164 4 1 18 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 72 164 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 72 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 72 164 2 1 36 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 72 164 (accept_3_2 1 72 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 72 164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 71 164
  (allA_succ_of_accept 70 71 164 (accept_3_2 70 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 71 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 71 164 (accept_3_2 67 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 71 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 71 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 71 164 (accept_3_2 64 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 71 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 62 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 71 164 (accept_3_2 61 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 71 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 71 164
  (Polychromatic418967fa.accept_8_3_7_4_1_42 59 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 71 164 (accept_3_2 58 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 71 164 (Polychromatic418967fa.accept_16_8_7_4_1_2217 56 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 71 164 (accept_3_2 55 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 71 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 71 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 71 164 (accept_3_2 52 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 71 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 71 164 (accept_3_2 49 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 71 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 71 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 71 164 (accept_3_2 46 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 71 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 71 164 (accept_3_2 43 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 71 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 71 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 71 164 (accept_3_2 40 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 71 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 71 164 (accept_3_2 37 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 71 164 (Polychromatic418967fa.accept_17_2_3_11_1_2919 36 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 71 164
  (Polychromatic418967fa.accept_8_3_7_4_1_42 35 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 71 164 (accept_3_2 34 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 71 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 71 164 (accept_3_2 31 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 71 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 71 164
  (Polychromatic418967fa.accept_16_13_7_4_1_3248 29 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 71 164 (accept_3_2 28 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 71 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 71 164 (accept_3_2 25 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 71 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 71 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 71 164 (accept_3_2 22 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 71 164 (Polychromatic418967fa.accept_21_20_8_17_1_7437 20 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 71 164 (accept_3_2 19 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 71 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 71 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 71 164
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 17 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 71 164 (accept_3_2 16 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 71 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 71 164 (accept_3_2 13 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 71 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 71 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 71 164 (accept_3_2 10 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  71 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 71 164 (Polychromatic418967fa.accept_16_8_7_4_1_2217 8 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 71 164 (accept_3_2 7 71 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 71 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 71 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 71 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 71 164 (accept_3_2 4 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 71
  164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 71 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 71 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 71 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 71 164 (accept_3_2 1 71 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 71 164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 70 164
  (allA_of_3_0 70 70 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 69 164 (allA_succ_of_accept 68 69 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 69 164 (accept_3_2 67 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66
  69 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 69 164 (accept_3_2 64 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 69 164 (Polychromatic418967fa.accept_10_3_9_4_1_960 63 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 69 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 69 164 (accept_3_2 61 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  69 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 69 164 (accept_3_2 58 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 69 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 57 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 69 164
  (Polychromatic418967fa.accept_16_8_5_4_1_674 56 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 69 164 (accept_3_2 55 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  69 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 69 164 (accept_3_2 52 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 69 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 69 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 69 164 (accept_3_2 49 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  69 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 69 164 (accept_3_2 46 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 69 164 (Polychromatic418967fa.accept_10_5_9_4_1_1420 45 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 69 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 69 164 (accept_3_2 43 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  69 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 69 164 (accept_3_2 40 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 69 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 69 164
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 69 164 (accept_3_2 37 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  69 164 (Polychromatic418967fa.accept_13_10_4_8_1_2570 36 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 69 164 (accept_3_2 34 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 69 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 69 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 69 164 (accept_3_2 31 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  69 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 69 164 (accept_3_2 28 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 69 164 (Polychromatic418967fa.accept_15_12_9_14_1_2635 27 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 69 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 69 164 (accept_3_2 25 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  69 164 (Polychromatic418967fa.accept_13_11_4_8_1_1098 24 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 69 164 (accept_3_2 22 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 69 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 69 164
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 20 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 69 164 (accept_3_2 19 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  69 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 69 164 (accept_3_2 16 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 69 164 (Polychromatic418967fa.accept_10_5_9_4_1_1420 15 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 69 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 69 164 (accept_3_2 13 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  69 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 69 164 (accept_3_2 10 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 69 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 69 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 69 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 69 164 (accept_3_2 7 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 69
  164 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 69 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 69 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 69 164 (accept_3_2 4 69 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 69 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 69 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 69 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  69 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 69 164 (accept_3_2 1 69 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 69
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 68 164 (allA_succ_of_accept 67 68
  164 (accept_3_2 67 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 68 164 2 33 34 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 68 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 65 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 68 164 4 16 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 68 164 (Polychromatic418967fa.accept_13_11_3_8_1_1786 63 68 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 68 164 2 31 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 68 164 (accept_3_2 61 68 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 68 164 4 15 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 68 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 68 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 68 164 2 29 34 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 68 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 68 164 4 14 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 68 164 (accept_3_2 55 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 68
  164 2 27 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  68 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 68 164 4 13 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 68 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 68 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 68 164 2 25 34 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 68 164 (accept_3_2 49 68 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 68 164 4 12 17 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 68 164
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 68 164 2 23 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 68 164 (Polychromatic418967fa.accept_11_1_2_10_1_1426 45 68 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 68 164 4 11 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 68 164 (accept_3_2 43 68 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 68 164 2 21 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 68 164 (Polychromatic418967fa.accept_19_3_11_12_1_9102 41 68
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 68 164 4 10 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 68 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 68 164 2 19 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 68 164 (accept_3_2 37 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 68
  164 4 9 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  68 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 68 164 2 17 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 68 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 33 68 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 68 164 4 8 17 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 68 164 (accept_3_2 31 68 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 68 164 2 15 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 68 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 68 164 4 7 17 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 68 164
  (Polychromatic418967fa.accept_19_8_11_12_1_6165 27 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 68 164 2 13 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 68 164 (accept_3_2 25 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 68
  164 4 6 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  68 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 68 164 2 11 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 68 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 68 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 68 164 4 5 17 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 68 164 (accept_3_2 19 68 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 68 164 2 9 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 68 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 68 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 68 164 4 4 17 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 68 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 68 164 2 7 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 68 164 (accept_3_2 13 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 68
  164 4 3 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  68 164 (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 68 164 2 5 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 68 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 68 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 68 164 4 2 17 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 68 164 (accept_3_2 7 68 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 68 164 2 3 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 68 164 (Polychromatic418967fa.accept_13_5_3_8_1_1117 5 68 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 68 164 4 1 17 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 68 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 68 164 2 1 34 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 68 164 (accept_3_2 1 68 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 68
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 67 164 (allA_of_3_0 67 67 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 66 164 (allA_succ_of_accept 65 66 164
  (Polychromatic418967fa.accept_10_5_6_4_1_64 65 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 66 164 2 32 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 66 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 63 66 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 66 164 2 31 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 66 164 (accept_3_2 61 66 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 66 164 2 30 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 66 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 66 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 66 164 2 29 33 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 66 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 66 164 2 28 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 66 164 (accept_3_2 55 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 66
  164 2 27 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53
  66 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 66 164 2 26 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 66 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 66 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 66 164 2 25 33 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 66 164 (accept_3_2 49 66 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 66 164 2 24 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 66 164
  (Polychromatic418967fa.accept_17_13_15_11_1_2936 47 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 66 164 2 23 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 66 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 66 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 66 164 2 22 33 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 66 164 (accept_3_2 43 66 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 66 164 2 21 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 66 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 41 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 66 164 2 20 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 66 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 66 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 66 164 2 19 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 66 164 (accept_3_2 37 66 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 66 164 2 18 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 66 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 66 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 66 164 2 17 33 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 66 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 66 164 2 16 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 66 164 (accept_3_2 31 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 66
  164 2 15 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  66 164 (Polychromatic418967fa.accept_19_10_9_12_1_4774 29 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 66 164 2 14 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 66 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 27 66 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 66 164 2 13 33 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 66 164 (accept_3_2 25 66 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 66 164 2 12 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 66 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 23 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 66 164 2 11 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 66 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 66 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 66 164 2 10 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 66 164 (accept_3_2 19 66 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 66 164 2 9 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 66 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 66 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 66 164 2 8 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 66 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 66 164 2 7 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 66 164 (accept_3_2 13 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 66
  164 2 6 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  66 164 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 66 164 2 5 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 66 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 66 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 66 164 2 4 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 66 164 (accept_3_2 7 66 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 66 164 2 3 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 66 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 66 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 66 164 2 2 33 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 66 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 66 164 2 1 33 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 66 164 (accept_3_2 1 66 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 66
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 65 164 (allA_succ_of_accept 64 65 164
  (accept_3_2 64 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 65 164
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 65 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 62 65 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 65 164 (accept_3_2 61 65 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 65 164 (Polychromatic418967fa.accept_16_12_1_4_1_5403 60 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 65 164
  (Polychromatic418967fa.accept_10_9_5_4_1_966 59 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 65 164 (accept_3_2 58 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 65 164 (Polychromatic418967fa.accept_10_6_5_4_1_571 56 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 65 164 (accept_3_2 55 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 65 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 65 164
  (Polychromatic418967fa.accept_8_5_1_4_1_628 53 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 65 164 (accept_3_2 52 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 65 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 65 164 (accept_3_2 49 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 65 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 65 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 65 164 (accept_3_2 46 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 65 164 (Polychromatic418967fa.accept_16_12_1_4_1_5403 44 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 65 164 (accept_3_2 43 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 65 164 (Polychromatic418967fa.accept_17_8_14_11_1_9101 42 65
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 65 164
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 65 164 (accept_3_2 40 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 65 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 38 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 65 164 (accept_3_2 37 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 65 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 65 164
  (Polychromatic418967fa.accept_16_3_1_4_1_5426 35 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 65 164 (accept_3_2 34 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 65 164 (Polychromatic418967fa.accept_15_2_5_14_1_61 32 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 65 164 (accept_3_2 31 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 65 164 (Polychromatic418967fa.accept_16_14_1_4_1_5432 30 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 65 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 65 164 (accept_3_2 28 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 65 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 65 164 (accept_3_2 25 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 65 164 (Polychromatic418967fa.accept_15_9_5_14_1_973 24 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 65 164
  (Polychromatic418967fa.accept_15_8_5_14_1_986 23 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 65 164 (accept_3_2 22 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 65 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 65 164 (accept_3_2 19 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 65 164 (Polychromatic418967fa.accept_22_18_21_10_1_9100 18 65 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 65 164
  (Polychromatic418967fa.accept_15_2_5_14_1_61 17 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 65 164 (accept_3_2 16 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 65 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 14 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 65 164 (accept_3_2 13 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 65 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 65 164
  (Polychromatic418967fa.accept_10_1_5_4_1_276 11 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 65 164 (accept_3_2 10 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  65 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 65 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 65 164 (accept_3_2 7 65 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 65 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 65 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 65 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 65 164 (accept_3_2 4 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 65
  164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 65 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 65 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 2 65 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 65 164 (accept_3_2 1 65 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 65 164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 64 164
  (allA_of_3_0 64 64 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 63 164 (allA_succ_of_accept 62 63 164
  (Polychromatic418967fa.accept_13_10_11_8_1_1770 62 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 63 164 (accept_3_2 61 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60
  63 164 (Polychromatic418967fa.accept_14_4_7_10_1_3888 60 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 63 164 (accept_3_2 58 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 63 164 (Polychromatic418967fa.accept_10_7_3_4_1_978 57 63 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 63 164
  (Polychromatic418967fa.accept_13_4_11_8_1_1768 56 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 63 164 (accept_3_2 55 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  63 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 63 164 (accept_3_2 52 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 63 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 51 63 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 63 164
  (Polychromatic418967fa.accept_17_16_12_11_1_6504 50 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 63 164 (accept_3_2 49 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 63 164 (Polychromatic418967fa.accept_13_9_11_8_1_195 48 63 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 63 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 63 164 (accept_3_2 46 63 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 63 164 (Polychromatic418967fa.accept_13_6_11_8_1_1111
  45 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 63 164
  (Polychromatic418967fa.accept_16_12_15_4_1_5422 44 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 63 164 (accept_3_2 43 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  63 164 (Polychromatic418967fa.accept_11_9_8_10_1_934 42 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 63 164 (accept_3_2 40 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 63 164 (Polychromatic418967fa.accept_10_9_3_4_1_985 39 63 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 63 164
  (Polychromatic418967fa.accept_27_11_9_2_1_3160 38 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 63 164 (accept_3_2 37 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  63 164 (Polychromatic418967fa.accept_13_10_11_8_1_1770 36 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 63 164 (accept_3_2 34 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 63 164 (Polychromatic418967fa.accept_17_16_12_11_1_6504 33 63 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 63 164
  (Polychromatic418967fa.accept_13_6_11_8_1_1111 32 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 63 164 (accept_3_2 31 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  63 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 63 164 (accept_3_2 28 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 63 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 63 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 63 164
  (Polychromatic418967fa.accept_15_11_3_14_1_971 26 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 63 164 (accept_3_2 25 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  63 164 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 63 164 (accept_3_2 22 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 63 164 (Polychromatic418967fa.accept_16_5_15_4_1_9099 21 63 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 63 164
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 63 164 (accept_3_2 19 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  63 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 63 164 (accept_3_2 16 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 63 164 (Polychromatic418967fa.accept_19_15_6_12_1_7746 15 63 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 63 164
  (Polychromatic418967fa.accept_13_1_11_8_1_2562 14 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 63 164 (accept_3_2 13 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  63 164 (Polychromatic418967fa.accept_16_12_15_4_1_5422 12 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 63 164 (accept_3_2 10 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 63 164 (Polychromatic418967fa.accept_10_9_3_4_1_985 9 63 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 63 164
  (Polychromatic418967fa.accept_16_8_15_4_1_5402 8 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 63 164 (accept_3_2 7 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 63
  164 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 63 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 63 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 63 164 (accept_3_2 4 63 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 63 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 63 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 63 164 (Polychromatic418967fa.accept_15_2_3_14_1_972 2
  63 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 63 164 (accept_3_2 1 63 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 63
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 62 164 (allA_succ_of_accept 61 62 164
  (accept_3_2 61 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 62 164 2 30 31 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 62 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 59 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 62 164 2 29 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 62 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 57 62 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 62 164 2 28 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 62 164 (accept_3_2 55 62 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 62 164 2 27 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 62 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 62 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 62 164 2 26 31 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 62 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 51 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 62 164 2 25 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 62 164 (accept_3_2 49 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 62
  164 2 24 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  62 164 (Polychromatic418967fa.accept_10_7_2_4_1_569 47 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 62 164 2 23 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 62 164 (Polychromatic418967fa.accept_14_3_6_10_1_752 45 62 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 62 164 2 22 31 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 62 164 (accept_3_2 43 62 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 62 164 2 21 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 62 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 62 164 2 20 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 62 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 62 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 62 164 2 19 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 62 164 (accept_3_2 37 62 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 62 164 2 18 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 62 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 62 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 62 164 2 17 31 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 62 164
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 62 164 2 16 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 62 164 (accept_3_2 31 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 62
  164 2 15 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  62 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 62 164 2 14 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 62 164 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 62 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 62 164 2 13 31 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 62 164 (accept_3_2 25 62 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 62 164 2 12 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 62 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 62 164 2 11 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 62 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 62 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 62 164 2 10 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 62 164 (accept_3_2 19 62 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 62 164 2 9 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 62 164 (Polychromatic418967fa.accept_10_7_2_4_1_569 17 62 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 62 164 2 8 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 62 164
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 62 164 2 7 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 62 164 (accept_3_2 13 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 62
  164 2 6 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  62 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 62 164 2 5 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 62 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 62 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 62 164 2 4 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 62 164 (accept_3_2 7 62 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 62 164 2 3 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 62 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 62 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 62 164 2 2 31 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 62 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 62 164 2 1 31 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 62 164 (accept_3_2 1 62 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 62
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 61 164 (allA_of_3_0 61 61 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 60 164 (allA_succ_of_accept 59 60 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 59 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 60 164 2 29 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 60 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 60 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 60 164 4 14 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 60 164 (accept_3_2 55 60 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 60 164 2 27 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 60 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 60 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 60 164 4 13 15 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 60 164
  (Polychromatic418967fa.accept_16_3_12_4_1_170 51 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 60 164 2 25 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 60 164 (accept_3_2 49 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 60
  164 4 12 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47
  60 164 (Polychromatic418967fa.accept_16_15_12_4_1_4324 47 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 60 164 2 23 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 60 164 (Polychromatic418967fa.accept_16_13_12_4_1_4323 45 60 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 60 164 4 11 15 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 60 164 (accept_3_2 43 60 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 60 164 2 21 30 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 60 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 41 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 60 164 4 10 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 60 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 60 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 60 164 2 19 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 60 164 (accept_3_2 37 60 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 60 164 4 9 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 60 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 60 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 60 164 2 17 30 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 60 164
  (Polychromatic418967fa.accept_16_1_12_4_1_695 33 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 60 164 4 8 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 60 164 (accept_3_2 31 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 60
  164 2 15 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  60 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 60 164 4 7 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 60 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 60 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 60 164 2 13 30 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 60 164 (accept_3_2 25 60 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 60 164 4 6 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 60 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 60 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 60 164 2 11 30 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 60 164
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 60 164 4 5 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 60 164 (accept_3_2 19 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 60
  164 2 9 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  60 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 60 164 4 4 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 60 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 60 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 60 164 2 7 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 60 164 (accept_3_2 13 60 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 60 164 4 3 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 60 164 (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 60 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 60 164 2 5 30 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 60 164
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 60 164 4 2 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 60 164 (accept_3_2 7 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 60 164
  2 3 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 60
  164 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 60 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 60 164 4 1 15 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 60 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 60 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 60 164 2 1 30 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 60 164 (accept_3_2 1 60 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 60 164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 59 164
  (allA_succ_of_accept 58 59 164 (accept_3_2 58 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57
  59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 59 164 (Polychromatic418967fa.accept_16_8_11_4_1_3290 56 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 59 164 (accept_3_2 55 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 59 164 (Polychromatic418967fa.accept_13_2_7_8_1_4221 54 59 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 59 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 59 164 (accept_3_2 52 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51
  59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 59 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 59 164 (accept_3_2 49 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 59 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 59 164
  (Polychromatic418967fa.accept_8_7_3_4_1_404 47 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 59 164 (accept_3_2 46 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45
  59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 59 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 59 164 (accept_3_2 43 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 59 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 59 164
  (Polychromatic418967fa.accept_13_2_7_8_1_4221 41 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 59 164 (accept_3_2 40 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39
  59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 59 164 (Polychromatic418967fa.accept_10_8_9_4_1_961 38 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 59 164 (accept_3_2 37 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 59 164 (Polychromatic418967fa.accept_13_10_7_8_1_1794 36 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 59 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 59 164 (accept_3_2 34 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33
  59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 59 164 (Polychromatic418967fa.accept_23_9_13_3_1_7305 32 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 59 164 (accept_3_2 31 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 59 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 59 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 59 164
  (Polychromatic418967fa.accept_13_3_7_8_1_4192 29 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 59 164 (accept_3_2 28 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27
  59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 59 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 59 164 (accept_3_2 25 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 59 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 59 164
  (Polychromatic418967fa.accept_8_7_3_4_1_404 23 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 59 164 (accept_3_2 22 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 59 164 (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 59 164 (accept_3_2 19 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 59 164 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 59 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 59 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 59 164 (accept_3_2 16 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 59 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 59 164 (accept_3_2 13 59 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 59 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 59 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 59 164
  (Polychromatic418967fa.accept_22_11_15_10_1_9098 11 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 59 164 (accept_3_2 10 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 59 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 59 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 59 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 8 59 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 59 164 (accept_3_2 7 59 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 59 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 6
  59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 59 164
  (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 59 164 (accept_3_2 4 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 59
  164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 59 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 59 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 59 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 59 164 (accept_3_2 1 59 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 59 164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 58 164 (allA_of_3_0
  58 58 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 57 164 (allA_succ_of_accept 56 57 164
  (Polychromatic418967fa.accept_11_1_2_10_1_1426 56 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 57 164 (accept_3_2 55 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54
  57 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 54 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 57 164 (accept_3_2 52 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 57 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 57 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 57 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 57 164 (accept_3_2 49 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48
  57 164 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 57 164 (accept_3_2 46 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 57 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 45 57 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 57 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 57 164 (accept_3_2 43 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  57 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 57 164 (accept_3_2 40 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 57 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 57 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 57 164
  (Polychromatic418967fa.accept_13_12_5_8_1_1101 38 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 57 164 (accept_3_2 37 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  57 164 (Polychromatic418967fa.accept_13_10_5_8_1_2555 36 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 57 164 (accept_3_2 34 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 57 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 57 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 57 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 32 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 57 164 (accept_3_2 31 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  57 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 57 164 (accept_3_2 28 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 57 164 (Polychromatic418967fa.accept_13_1_5_8_1_207 27 57 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 57 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 57 164 (accept_3_2 25 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  57 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 57 164 (accept_3_2 22 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 57 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 57 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 57 164
  (Polychromatic418967fa.accept_25_20_7_14_1_9097 20 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 57 164 (accept_3_2 19 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  57 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 57 164 (accept_3_2 16 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 57 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 57 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 57 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 57 164 (accept_3_2 13 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  57 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 57 164 (accept_3_2 10 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 57 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 57 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 57 164
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 57 164 (accept_3_2 7 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 57
  164 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 57 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 57 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 57 164 (accept_3_2 4 57 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 57 164 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 57 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 57 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  57 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 57 164 (accept_3_2 1 57 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 57 164)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 56 164 (allA_succ_of_accept 55 56 164 (accept_3_2 55 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 56 164 2 27 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 56 164 (Polychromatic418967fa.accept_11_9_1_10_1_920 53 56 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 56 164 4 13 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 56 164 (Polychromatic418967fa.accept_13_12_4_8_1_1120
  51 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 56 164 2 25 28 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 56 164 (accept_3_2 49
  56 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 56 164 4 12 14 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 56 164
  (Polychromatic418967fa.accept_16_15_8_4_1_1355 47 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 56 164 2 23 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 56 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 56 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 56 164 4 11 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 56 164 (accept_3_2 43 56 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 56 164 2 21 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 56 164 (Polychromatic418967fa.accept_16_9_8_4_1_1354 41 56 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 56 164 4 10 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 56 164
  (Polychromatic418967fa.accept_16_7_8_4_1_689 39 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 56 164 2 19 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 56 164 (accept_3_2 37 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 56
  164 4 9 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  56 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 56 164 2 17 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 56 164 (Polychromatic418967fa.accept_15_3_11_14_1_1705 33 56 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 56 164 4 8 14 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 56 164 (accept_3_2 31 56 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 56 164 2 15 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 56 164 (Polychromatic418967fa.accept_16_13_8_4_1_3250
  29 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 56 164 4 7 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 56 164
  (Polychromatic418967fa.accept_15_12_11_14_1_3464 27 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 56 164 2 13 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 56 164 (accept_3_2 25 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 56 164 4 6 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 56 164 (Polychromatic418967fa.accept_13_10_4_8_1_2570 23 56 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 56 164 2 11 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 56 164 (Polychromatic418967fa.accept_16_5_8_4_1_5418
  21 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 56 164 4 5 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 56 164 (accept_3_2 19
  56 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 56 164 2 9 28 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 56 164
  (Polychromatic418967fa.accept_16_1_8_4_1_4334 17 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 56 164 4 4 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 56 164 (Polychromatic418967fa.accept_10_5_6_4_1_64 15 56 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 56 164 2 7 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 56 164 (accept_3_2 13 56 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 56 164 4 3 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 56 164 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 56 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 56 164 2 5 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 56 164 (Polychromatic418967fa.accept_11_9_1_10_1_920 9
  56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 56 164 4 2 14 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 56 164 (accept_3_2 7 56
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 56 164 2 3 28 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 56 164
  (Polychromatic418967fa.accept_10_5_6_4_1_64 5 56 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 56 164 4 1 14 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 56 164 (Polychromatic418967fa.accept_15_3_11_14_1_1705 3 56 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 56 164 2 1 28 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 56 164 (accept_3_2 1 56 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 56 164)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 55 164 (allA_of_3_0 55
  55 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 54 164 (allA_succ_of_accept 53 54 164
  (Polychromatic418967fa.accept_15_8_9_14_1_4577 53 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 54 164 2 26 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 54 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 54 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 54 164 2 25 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 54 164 (accept_3_2 49 54 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 48 54 164 2 24 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 54 164 (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 54
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 54 164 2 23 27 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 54 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 54 164 2 22 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 43 54 164 (accept_3_2 43 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 54
  164 2 21 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41
  54 164 (Polychromatic418967fa.accept_23_18_8_3_1_9096 41 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 54 164 2 20 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 54 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 39 54 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 54 164 2 19 27 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 54 164 (accept_3_2 37 54 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 54 164 2 18 27 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 54 164
  (Polychromatic418967fa.accept_15_5_9_14_1_1724 35 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 54 164 2 17 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 54 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 33 54 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 54 164 2 16 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 54 164 (accept_3_2 31 54 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 54 164 2 15 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 54 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 54 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 54 164 2 14 27 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 54 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 54 164 2 13 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 54 164 (accept_3_2 25 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 54
  164 2 12 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  54 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 54 164 2 11 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 54 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 21 54 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 54 164 2 10 27 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 54 164 (accept_3_2 19 54 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 54 164 2 9 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 54 164 (Polychromatic418967fa.accept_23_17_8_3_1_9095
  17 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 54 164 2 8 27 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 54 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 54 164 2 7 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 54 164 (accept_3_2 13 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 54
  164 2 6 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  54 164 (Polychromatic418967fa.accept_16_11_6_4_1_2228 11 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 54 164 2 5 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 54 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 54 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 54 164 2 4 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 54 164 (accept_3_2 7 54 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 54 164 2 3 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 54 164 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 54 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 54 164 2 2 27 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 54 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 3 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 54 164 2 1 27 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 54 164 (accept_3_2 1 54 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 54
  164)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 53 164 (allA_succ_of_accept 52 53 164 (accept_3_2
  52 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 53 164
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 53 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 53 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 53 164 (accept_3_2 49 53 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 53 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 53 164 (Polychromatic418967fa.accept_10_7_3_4_1_978
  47 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 53 164 (accept_3_2 46
  53 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 53 164
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 53 164 (Polychromatic418967fa.accept_13_5_1_8_1_1115 44 53 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 53 164 (accept_3_2 43 53 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 53 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 53 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 53 164 (accept_3_2 40 53
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 53 164 (Polychromatic418967fa.accept_6_3_5_2_1_12
  39 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 53 164
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 53 164 (accept_3_2 37 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  53 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 53 164 (Polychromatic418967fa.accept_13_9_1_8_1_1742 35 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 53 164 (accept_3_2 34 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 53 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 53 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 53 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 53 164 (accept_3_2 31 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  53 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 53 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 53 164 (accept_3_2 28 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 53 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 53 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 53 164
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 53 164 (accept_3_2 25 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  53 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 53 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 53 164 (accept_3_2 22 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 53 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 53 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 53 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 53 164 (accept_3_2 19 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  53 164 (Polychromatic418967fa.accept_13_5_1_8_1_1115 18 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 53 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 17 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 53 164 (accept_3_2 16 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 53 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 53 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 53 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 53 164 (accept_3_2 13 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  53 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 53 164 (Polychromatic418967fa.accept_13_11_1_8_1_1776 11 53 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 53 164 (accept_3_2 10 53 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 53 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 53 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 53 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 53 164 (accept_3_2 7 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 53
  164 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 53 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 53 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 53 164 (accept_3_2 4 53 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 53 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 53 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 53 164 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  53 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 53 164 (accept_3_2 1 53 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 53 164)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 52 164 (allA_of_3_0 52 52 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 51 164
  (allA_succ_of_accept 50 51 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 51 164 (accept_3_2 49 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 51 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 51 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 51 164 (accept_3_2 46 51
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 51 164
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 45 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 51 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 51 164 (accept_3_2 43 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 51 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 51 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41
  51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 51 164 (accept_3_2 40 51
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 51 164
  (Polychromatic418967fa.accept_8_7_3_4_1_404 39 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 51 164 (Polychromatic418967fa.accept_15_8_6_14_1_975 38 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 51 164 (accept_3_2 37 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 51 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 51 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35
  51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 51 164 (accept_3_2 34 51
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 51 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 51 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 51 164 (accept_3_2 31 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 51 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 51 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 51 164 (accept_3_2 28 51
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 51 164
  (Polychromatic418967fa.accept_7_6_2_3_1_107 27 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 51 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 51 164 (accept_3_2 25 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 51 164 (Polychromatic418967fa.accept_15_9_6_14_1_2627 24 51 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 51 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 51 164 (accept_3_2 22 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  51 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 51 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 51 164 (accept_3_2 19 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 51 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 51 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 51 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 51 164 (accept_3_2 16 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  51 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 51 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 51 164 (accept_3_2 13 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 51 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 51 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 51 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 51 164 (accept_3_2 10 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  51 164 (Polychromatic418967fa.accept_13_9_12_8_1_570 9 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 51 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 51 164 (accept_3_2 7 51 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 51 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 51 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 51 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 51 164 (accept_3_2 4 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 51
  164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 51 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 51 164 (Polychromatic418967fa.accept_21_2_9_17_1_4376 2 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 51 164 (accept_3_2 1 51 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 51 164))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 50 164 (allA_succ_of_accept
  49 50 164 (accept_3_2 49 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 50 164 2 24 25 82
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 50 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 50 164 2 23 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 50 164 (Polychromatic418967fa.accept_13_6_11_8_1_1111 45 50 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 50 164 2 22 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 50 164 (accept_3_2 43 50 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 50 164 2 21 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 50 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 50 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 50 164 2 20 25 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 50 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 50 164 2 19 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 50 164 (accept_3_2 37 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 50
  164 2 18 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  50 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 50 164 2 17 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 50 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 50 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 50 164 2 16 25 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 50 164 (accept_3_2 31 50 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 50 164 2 15 25 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 50 164
  (Polychromatic418967fa.accept_12_5_2_8_1_172 29 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 50 164 2 14 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 50 164 (Polychromatic418967fa.accept_11_5_6_10_1_1432 27 50 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 50 164 2 13 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 50 164 (accept_3_2 25 50 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 50 164 2 12 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 50 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 50 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 50 164 2 11 25 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 50 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 50 164 2 10 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 50 164 (accept_3_2 19 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 50
  164 2 9 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  50 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 50 164 2 8 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 50 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 15 50 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 50 164 2 7 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 50 164 (accept_3_2 13 50 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 50 164 2 6 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 50 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 50 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 50 164 2 5 25 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 50 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 50 164 2 4 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 50 164 (accept_3_2 7 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 50 164
  2 3 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 50
  164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 50 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 50 164 2 2 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 50 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 50 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 50 164 2 1 25 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 50 164 (accept_3_2 1 50 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 50 164)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 49 164 (allA_of_3_0 49 49
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 48 164 (allA_succ_of_accept 47 48 164
  (Polychromatic418967fa.accept_15_2_3_14_1_972 47 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 48 164 2 23 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 48 164 (Polychromatic418967fa.accept_14_3_6_10_1_752 45 48 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 48 164 4 11 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 48 164 (accept_3_2 43 48 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 42 48 164 2 21 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 48 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 48 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 48 164 4 10 12 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 48 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 48 164 2 19 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 37 48 164 (accept_3_2 37 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 48
  164 4 9 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  48 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 48 164 2 17 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 48 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 48 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 48 164 4 8 12 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 48 164 (accept_3_2 31 48 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 48 164 2 15 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 48 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 29
  48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 48 164 4 7 12 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 48 164
  (Polychromatic418967fa.accept_11_5_4_10_1_524 27 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 48 164 2 13 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 48 164 (accept_3_2 25 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 48
  164 4 6 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  48 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 48 164 2 11 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 48 164 (Polychromatic418967fa.accept_18_3_12_2_1_2639 21 48 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 48 164 4 5 12 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 48 164 (accept_3_2 19 48 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 48 164 2 9 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 48 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 48 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 48 164 4 4 12 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 48 164
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 48 164 2 7 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 48 164 (accept_3_2 13 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 48
  164 4 3 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  48 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 48 164 2 5 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 48 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 48 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 48 164 4 2 12 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 48 164 (accept_3_2 7 48 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 48 164 2 3 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 48 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 48 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 48 164 4 1 12 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 48 164
  (Polychromatic418967fa.accept_13_3_9_8_1_4202 3 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 48 164 2 1 24 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 48 164 (accept_3_2 1 48 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 48
  164)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 47 164 (allA_succ_of_accept 46 47 164 (accept_3_2 46 47
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 47 164 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 47 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 44 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 47 164 (accept_3_2 43 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42
  47 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 42 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 47 164 (Polychromatic418967fa.accept_10_1_7_4_1_968 41 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 47 164 (accept_3_2 40 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 47 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 47 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 47 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 47 164 (accept_3_2 37 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  47 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 47 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 47 164 (accept_3_2 34 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 47 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 47 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 47 164
  (Polychromatic418967fa.accept_10_2_7_4_1_967 32 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 47 164 (accept_3_2 31 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  47 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 47 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 47 164 (accept_3_2 28 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 47 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 47 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 47 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 47 164 (accept_3_2 25 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  47 164 (Polychromatic418967fa.accept_16_8_15_4_1_5402 24 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 47 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 47 164 (accept_3_2 22 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 47 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 47 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 47 164
  (Polychromatic418967fa.accept_15_5_2_14_1_1693 20 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 47 164 (accept_3_2 19 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  47 164 (Polychromatic418967fa.accept_11_7_3_10_1_1461 18 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 47 164 (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 47 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 47 164 (accept_3_2 16 47 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 47 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 47 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 47 164
  (Polychromatic418967fa.accept_12_2_11_8_1_504 14 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 47 164 (accept_3_2 13 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  47 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 47 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 11 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 47 164 (accept_3_2 10 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 47 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 47 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 47 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 47 164 (accept_3_2 7 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 47
  164 (Polychromatic418967fa.accept_17_6_13_11_1_995 6 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 47 164 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 47 164 (accept_3_2 4 47 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 47 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 47 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 47 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 47 164 (accept_3_2 1 47 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 47
  164))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 46 164 (allA_of_3_0 46 46 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 45 164 (allA_succ_of_accept 44 45 164 (Polychromatic418967fa.accept_16_12_13_4_1_3198
  44 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 45 164 (accept_3_2 43
  45 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 45 164
  (Polychromatic418967fa.accept_11_9_1_10_1_920 42 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 45 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 45 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 45 164 (accept_3_2 40 45 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 45 164 (Polychromatic418967fa.accept_10_9_5_4_1_966 39 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 45 164 (Polychromatic418967fa.accept_16_6_13_4_1_643
  38 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 45 164 (accept_3_2 37
  45 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 45 164
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 45 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 45 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 45 164 (accept_3_2 34 45 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 45 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 33 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 45 164
  (Polychromatic418967fa.accept_24_8_21_20_1_9094 32 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 45 164 (accept_3_2 31 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  45 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 45 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 45 164 (accept_3_2 28 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 45 164 (Polychromatic418967fa.accept_13_1_6_8_1_208 27 45 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 45 164
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 45 164 (accept_3_2 25 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  45 164 (Polychromatic418967fa.accept_11_2_1_10_1_196 24 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 45 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 45 164 (accept_3_2 22 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 45 164 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 45 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 45 164
  (Polychromatic418967fa.accept_11_9_1_10_1_920 20 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 45 164 (accept_3_2 19 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  45 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 45 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 45 164 (accept_3_2 16 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 45 164 (Polychromatic418967fa.accept_13_2_6_8_1_1092 15 45 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 45 164
  (Polychromatic418967fa.accept_13_1_6_8_1_208 14 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 45 164 (accept_3_2 13 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  45 164 (Polychromatic418967fa.accept_16_12_13_4_1_3198 12 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 45 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 45 164 (accept_3_2 10 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 45 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 45 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 45 164
  (Polychromatic418967fa.accept_16_8_13_4_1_3258 8 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 45 164 (accept_3_2 7 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 45
  164 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 45 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 45 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 45 164 (accept_3_2 4 45 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 45 164 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 45 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 45 164 (Polychromatic418967fa.accept_11_2_1_10_1_196 2
  45 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 45 164 (accept_3_2 1 45 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 45 164))))))))))))))))))))))))))))))))))))))))))))) (allB_succ 44
  164 (allA_succ_of_accept 43 44 164 (accept_3_2 43 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42
  44 164 2 21 22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  41 44 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 44 164 4 10 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 44 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 39 44 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 44 164 2 19 22 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 44 164 (accept_3_2 37 44 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 44 164 4 9 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 44 164 (Polychromatic418967fa.accept_16_3_12_4_1_170
  35 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 44 164 2 17 22 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 44 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 33 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 44 164 4 8 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 44 164 (accept_3_2 31 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 44
  164 2 15 22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  44 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 44 164 4 7 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 44 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 44 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 44 164 2 13 22 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 44 164 (accept_3_2 25 44 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 44 164 4 6 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 44 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 44 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 44 164 2 11 22 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 44 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 44 164 4 5 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 44 164 (accept_3_2 19 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 44
  164 2 9 22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  44 164 (Polychromatic418967fa.accept_16_1_12_4_1_695 17 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 44 164 4 4 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 44 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 44 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 44 164 2 7 22 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 44 164 (accept_3_2 13 44 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 44 164 4 3 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 44 164 (Polychromatic418967fa.accept_16_11_12_4_1_3195 11 44 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 44 164 2 5 22 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 44 164
  (Polychromatic418967fa.accept_16_9_12_4_1_3255 9 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 44 164 4 2 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 44 164 (accept_3_2 7 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 44 164
  2 3 22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 44
  164 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 44 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 44 164 4 1 11 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 44 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 44 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 44 164 2 1 22 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 44 164 (accept_3_2 1 44 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 44 164)))))))))))))))))))))))))))))))))))))))))))) (allB_succ 43 164 (allA_of_3_0 43 43 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 42 164 (allA_succ_of_accept 41 42 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 42 164 2 20 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 42 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 42 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 42 164 2 19 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 42 164 (accept_3_2 37 42 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 42 164 2 18 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 42 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 42 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 42 164 2 17 21 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 42 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 42 164 2 16 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 42 164 (accept_3_2 31 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 42
  164 2 15 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  42 164 (Polychromatic418967fa.accept_20_9_2_4_1_9093 29 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 42 164 2 14 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 42 164 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 42 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 42 164 2 13 21 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 42 164 (accept_3_2 25 42 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 42 164 2 12 21 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 42 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 23 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 42 164 2 11 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 42 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 42 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 42 164 2 10 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 42 164 (accept_3_2 19 42 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 18 42 164 2 9 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 42 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 42 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 42 164 2 8 21 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 42 164
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 42 164 2 7 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 42 164 (accept_3_2 13 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 42
  164 2 6 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  42 164 (Polychromatic418967fa.accept_13_11_3_8_1_1786 11 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 42 164 2 5 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 42 164 (Polychromatic418967fa.accept_12_9_6_8_1_518 9 42 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 42 164 2 4 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 42 164 (accept_3_2 7 42 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 42 164 2 3 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 42 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 42 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 42 164 2 2 21 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 42 164
  (Polychromatic418967fa.accept_9_3_6_2_1_160 3 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 42 164 2 1 21 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 42 164 (accept_3_2 1 42 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 42
  164)))))))))))))))))))))))))))))))))))))))))) (allB_succ 41 164 (allA_succ_of_accept 40 41 164 (accept_3_2 40 41 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 41 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 39
  41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 41 164
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 41 164 (accept_3_2 37 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  41 164 (Polychromatic418967fa.accept_13_10_2_8_1_2603 36 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 41 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 41 164 (accept_3_2 34 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 41 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 41 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 41 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 41 164 (accept_3_2 31 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  41 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 41 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 29 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 41 164 (accept_3_2 28 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 41 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 41 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 41 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 41 164 (accept_3_2 25 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  41 164 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 41 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 41 164 (accept_3_2 22 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 41 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 41 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 41 164
  (Polychromatic418967fa.accept_11_9_8_10_1_934 20 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 41 164 (accept_3_2 19 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  41 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 41 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 41 164 (accept_3_2 16 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 41 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 41 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 41 164
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 41 164 (accept_3_2 13 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  41 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 41 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 41 164 (accept_3_2 10 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 41 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 41 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 41 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 41 164 (accept_3_2 7 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 41
  164 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 41 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 41 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 41 164 (accept_3_2 4 41 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 41 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 41 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 41 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 2
  41 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 41 164 (accept_3_2 1 41 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 41 164))))))))))))))))))))))))))))))))))))))))) (allB_succ 40 164
  (allA_of_3_0 40 40 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 39 164 (allA_succ_of_accept 38 39 164
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 39 164 (accept_3_2 37 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36
  39 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 39 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 39 164 (accept_3_2 34 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 39 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 39 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 39 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 32 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 39 164 (accept_3_2 31 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  39 164 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 39 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 39 164 (accept_3_2 28 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 39 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 39 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 39 164
  (Polychromatic418967fa.accept_9_8_3_2_1_417 26 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 39 164 (accept_3_2 25 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  39 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 39 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 39 164 (accept_3_2 22 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 39 164 (Polychromatic418967fa.accept_14_7_11_10_1_2155 21 39 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 39 164
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 39 164 (accept_3_2 19 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  39 164 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 39 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 39 164 (accept_3_2 16 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 39 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 39 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 39 164
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 39 164 (accept_3_2 13 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  39 164 (Polychromatic418967fa.accept_15_12_9_14_1_2635 12 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 39 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 39 164 (accept_3_2 10 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 39 164 (Polychromatic418967fa.accept_18_9_3_2_1_3814 9 39 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 39 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 39 164 (accept_3_2 7 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 39
  164 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 39 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 39 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 39 164 (accept_3_2 4 39 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 39 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 39 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 39 164 (Polychromatic418967fa.accept_19_2_1_12_1_9092
  2 39 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 39 164 (accept_3_2 1 39
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 39 164))))))))))))))))))))))))))))))))))))))) (allB_succ 38 164
  (allA_succ_of_accept 37 38 164 (accept_3_2 37 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 38
  164 2 18 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35
  38 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 34 38 164 2 17 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 38 164 (Polychromatic418967fa.accept_13_7_12_8_1_199 33 38 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 38 164 2 16 19 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 38 164 (accept_3_2 31 38 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 38 164 2 15 19 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 38 164
  (Polychromatic418967fa.accept_10_9_8_4_1_970 29 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 38 164 2 14 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 38 164 (Polychromatic418967fa.accept_13_1_12_8_1_1818 27 38 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 38 164 2 13 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 38 164 (accept_3_2 25 38 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 38 164 2 12 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 38 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 38 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 38 164 2 11 19 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 38 164
  (Polychromatic418967fa.accept_15_6_8_14_1_4575 21 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 38 164 2 10 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 38 164 (accept_3_2 19 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 38
  164 2 9 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  38 164 (Polychromatic418967fa.accept_11_6_5_10_1_2724 17 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 38 164 2 8 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 38 164 (Polychromatic418967fa.accept_11_4_5_10_1_926 15 38 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 38 164 2 7 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 38 164 (accept_3_2 13 38 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 38 164 2 6 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 38 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 38 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 38 164 2 5 19 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 38 164
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 38 164 2 4 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 38 164 (accept_3_2 7 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 38 164
  2 3 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 38
  164 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 38 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 38 164 2 2 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 38 164 (Polychromatic418967fa.accept_16_3_6_4_1_679 3 38 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 38 164 2 1 19 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 38 164 (accept_3_2 1 38 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 38 164)))))))))))))))))))))))))))))))))))))) (allB_succ 37 164 (allA_of_3_0 37 37 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ 36 164 (allA_succ_of_accept 35 36 164
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 36 164 2 17 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 36 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 36 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 36 164 4 8 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 36 164 (accept_3_2 31 36 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 36 164 2 15 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 36 164 (Polychromatic418967fa.accept_11_7_3_10_1_1461 29 36 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 36 164 4 7 9 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 36 164
  (Polychromatic418967fa.accept_21_6_15_17_1_7388 27 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 36 164 2 13 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 36 164 (accept_3_2 25 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 36
  164 4 6 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23
  36 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 36 164 2 11 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 36 164 (Polychromatic418967fa.accept_19_2_17_12_1_6097 21 36 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 36 164 4 5 9 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 36 164 (accept_3_2 19 36 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 36 164 2 9 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 36 164 (Polychromatic418967fa.accept_13_4_10_8_1_1817 17 36 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 36 164 4 4 9 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 36 164
  (Polychromatic418967fa.accept_10_5_6_4_1_64 15 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 36 164 2 7 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 36 164 (accept_3_2 13 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 36
  164 4 3 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  36 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 36 164 2 5 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 36 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 36 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 36 164 4 2 9 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 36 164 (accept_3_2 7 36 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 36 164 2 3 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 36 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 36 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 36 164 4 1 9 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 36 164
  (Polychromatic418967fa.accept_17_3_2_11_1_1895 3 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 36 164 2 1 18 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 36 164 (accept_3_2 1 36 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 36
  164)))))))))))))))))))))))))))))))))))) (allB_succ 35 164 (allA_succ_of_accept 34 35 164 (accept_3_2 34 35 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 35 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 33
  35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 35 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 35 164 (accept_3_2 31 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  35 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 35 164 (Polychromatic418967fa.accept_10_9_5_4_1_966 29 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 35 164 (accept_3_2 28 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 35 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 35 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 35 164
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 35 164 (accept_3_2 25 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  35 164 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 35 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 23 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 35 164 (accept_3_2 22 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 35 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 35 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 35 164
  (Polychromatic418967fa.accept_13_7_9_8_1_188 20 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 35 164 (accept_3_2 19 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  35 164 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 35 164 (Polychromatic418967fa.accept_13_4_9_8_1_1736 17 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 35 164 (accept_3_2 16 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 35 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 35 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 35 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 35 164 (accept_3_2 13 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  35 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 35 164 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 35 164 (accept_3_2 10 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 35 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 35 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 35 164
  (Polychromatic418967fa.accept_15_8_5_14_1_986 8 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 35 164 (accept_3_2 7 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 35
  164 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 35 164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 35 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 35 164 (accept_3_2 4 35 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 35 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 35 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 35 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 2
  35 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 35 164 (accept_3_2 1 35 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 35 164))))))))))))))))))))))))))))))))))) (allB_succ 34 164
  (allA_of_3_0 34 34 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 33 164 (allA_succ_of_accept 32 33 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 33 164 (accept_3_2 31 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30
  33 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 33 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 33 164 (accept_3_2 28 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 33 164 (Polychromatic418967fa.accept_10_7_3_4_1_978 27 33 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 33 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 33 164 (accept_3_2 25 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24
  33 164 (Polychromatic418967fa.accept_16_8_1_4_1_6622 24 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 33 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 33 164 (accept_3_2 22 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 33 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 33 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 33 164
  (Polychromatic418967fa.accept_25_20_8_14_1_9091 20 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 33 164 (accept_3_2 19 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18
  33 164 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 33 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 33 164 (accept_3_2 16 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 33 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 33 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 33 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 33 164 (accept_3_2 13 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  33 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 33 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 33 164 (accept_3_2 10 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 33 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 33 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 33 164
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 33 164 (accept_3_2 7 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 33
  164 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 33 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 33 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 33 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 33 164 (accept_3_2 4 33 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 33 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 33 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 33 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 33
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 33 164 (accept_3_2 1 33 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 33 164))))))))))))))))))))))))))))))))) (allB_succ 32 164
  (allA_succ_of_accept 31 32 164 (accept_3_2 31 32 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 32
  164 2 15 16 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  32 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 32 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 32 164 4 7 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 32 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 32 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 32 164 2 13 16 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 32 164 (accept_3_2 25 32 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 32 164 4 6 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 32 164 (Polychromatic418967fa.accept_21_2_11_17_1_4395 23 32
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 32 164 2 11 16 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 32 164
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 32 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 32 164 4 5 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 32 164 (accept_3_2 19 32 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 32
  164 2 9 16 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  32 164 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 32 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 32 164 4 4 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 32 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 32 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 32 164 2 7 16 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 32 164 (accept_3_2 13 32 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 32 164 4 3 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 32 164 (Polychromatic418967fa.accept_13_11_6_8_1_1121 11 32 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 32 164 2 5 16 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 32 164
  (Polychromatic418967fa.accept_24_9_8_20_1_9090 9 32 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 32 164 4 2 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 32 164 (accept_3_2 7 32 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 32 164
  2 3 16 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 32
  164 (Polychromatic418967fa.accept_15_5_2_14_1_1693 5 32 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 32 164 4 1 8 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 32 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 32 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 32 164 2 1 16 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 32 164 (accept_3_2 1 32 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 32 164)))))))))))))))))))))))))))))))) (allB_succ 31 164 (allA_of_3_0 31 31 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 30 164 (allA_succ_of_accept 29 30 164
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 30 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 30 164 2 14 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 30 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 30 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 30 164 2 13 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 30 164 (accept_3_2 25 30 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 30 164 2 12 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 30 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 30 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 30 164 2 11 15 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 30 164
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 30 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 30 164 2 10 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 30 164 (accept_3_2 19 30 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 30
  164 2 9 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  30 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 30 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 30 164 2 8 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 30 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 30 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 30 164 2 7 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 30 164 (accept_3_2 13 30 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 30 164 2 6 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 30 164 (Polychromatic418967fa.accept_13_11_4_8_1_1098 11 30 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 30 164 2 5 15 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 30 164
  (Polychromatic418967fa.accept_11_9_8_10_1_934 9 30 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 30 164 2 4 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 30 164 (accept_3_2 7 30 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 30 164
  2 3 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 30
  164 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 30 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 30 164 2 2 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 30 164 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 30 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 30 164 2 1 15 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 30 164 (accept_3_2 1 30 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 30 164)))))))))))))))))))))))))))))) (allB_succ 29 164 (allA_succ_of_accept 28 29 164
  (accept_3_2 28 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 29 164
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 29 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 29 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 29 164 (accept_3_2 25 29 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 29 164 (Polychromatic418967fa.accept_13_11_3_8_1_1786 24 29 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 29 164
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 29 164 (accept_3_2 22 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21
  29 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 29 164 (Polychromatic418967fa.accept_13_7_3_8_1_1750 20 29 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 29 164 (accept_3_2 19 29 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 29 164 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 29 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 29 164
  (Polychromatic418967fa.accept_8_1_5_4_1_388 17 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 29 164 (accept_3_2 16 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  29 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 29 164 (Polychromatic418967fa.accept_11_3_7_10_1_180 14 29 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 29 164 (accept_3_2 13 29 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 29 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 29 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 29 164
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 29 164 (accept_3_2 10 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  29 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 29 164 (Polychromatic418967fa.accept_10_8_9_4_1_961 8 29 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 29 164 (accept_3_2 7 29 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 29 164 (Polychromatic418967fa.accept_16_6_13_4_1_643 6 29 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 29 164
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 29 164 (accept_3_2 4 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 29
  164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 29 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 29 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 29 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 29 164 (accept_3_2 1 29 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 29 164))))))))))))))))))))))))))))) (allB_succ 28 164 (allA_of_3_0 28 28 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 27 164 (allA_succ_of_accept 26 27 164 (Polychromatic418967fa.accept_11_4_5_10_1_926 26
  27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 27 164 (accept_3_2 25 27
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 27 164
  (Polychromatic418967fa.accept_13_11_1_8_1_1776 24 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 27 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 27 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 27 164 (accept_3_2 22 27 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 27 164 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 27 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 27 164 (Polychromatic418967fa.accept_13_7_1_8_1_1778
  20 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 27 164 (accept_3_2 19
  27 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 27 164
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 27 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 27 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 27 164 (accept_3_2 16 27 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 27 164 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 27 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 27 164
  (Polychromatic418967fa.accept_28_14_27_24_1_9089 14 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 27 164 (accept_3_2 13 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 27 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 27 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 27 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 27 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 27 164 (accept_3_2 10 27 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 27 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9
  27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 27 164
  (Polychromatic418967fa.accept_16_8_11_4_1_3290 8 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 27 164 (accept_3_2 7 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 27
  164 (Polychromatic418967fa.accept_11_6_5_10_1_2724 6 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 27 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 27 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 27 164 (accept_3_2 4 27 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 27 164 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 27 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 27 164
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 27 164 (accept_3_2 1 27 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 27
  164))))))))))))))))))))))))))) (allB_succ 26 164 (allA_succ_of_accept 25 26 164 (accept_3_2 25 26 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 26 164 2 12 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 26 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 23
  26 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 26 164 2 11 13 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 26 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 26 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 26 164 2 10 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 26 164 (accept_3_2 19 26 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 26
  164 2 9 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  26 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 26 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 26 164 2 8 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 26 164 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 26 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 26 164 2 7 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 26 164 (accept_3_2 13 26 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 26 164 2 6 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 26 164 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 26 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 26 164 2 5 13 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 26 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 26 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 26 164 2 4 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 26 164 (accept_3_2 7 26 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 26 164
  2 3 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 26
  164 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 26 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 26 164 2 2 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 26 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 26 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 26 164 2 1 13 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 26 164 (accept_3_2 1 26 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 26 164)))))))))))))))))))))))))) (allB_succ 25 164 (allA_of_3_0 25 25 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 24 164 (allA_succ_of_accept 23 24 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 23
  24 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 24 164 2 11 12 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 24 164
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 24 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 24 164 4 5 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 24 164 (accept_3_2 19 24 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 24
  164 2 9 12 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  24 164 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 24 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 24 164 4 4 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 24 164 (Polychromatic418967fa.accept_16_15_8_4_1_1355 15 24 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 24 164 2 7 12 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 24 164 (accept_3_2 13 24 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 24 164 4 3 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 24 164 (Polychromatic418967fa.accept_16_11_8_4_1_2234 11 24 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 24 164 2 5 12 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 24 164
  (Polychromatic418967fa.accept_13_9_11_8_1_195 9 24 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 24 164 4 2 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 24 164 (accept_3_2 7 24 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 24 164
  2 3 12 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 24
  164 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 24 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 24 164 4 1 6 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 24 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 24 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 24 164 2 1 12 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 24 164 (accept_3_2 1 24 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 24 164)))))))))))))))))))))))) (allB_succ 23 164 (allA_succ_of_accept 22 23 164 (accept_3_2 22
  23 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 23 164
  (Polychromatic418967fa.accept_6_3_5_2_1_12 21 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 23 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 23 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 23 164 (accept_3_2 19 23 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 23 164 (Polychromatic418967fa.accept_13_5_10_8_1_1127 18 23 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 23 164
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 23 164 (accept_3_2 16 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15
  23 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 23 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 23 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 23 164 (accept_3_2 13 23 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 23 164 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 23 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 23 164
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 23 164 (accept_3_2 10 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  23 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 23 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 23 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 23 164 (accept_3_2 7 23 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 23 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 23 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 23 164
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 23 164 (accept_3_2 4 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 23
  164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 23 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 23 164 (Polychromatic418967fa.accept_11_2_1_10_1_196 2 23 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 23 164 (accept_3_2 1 23 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 23 164))))))))))))))))))))))) (allB_succ 22 164 (allA_of_3_0 22 22 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ 21 164 (allA_succ_of_accept 20 21 164 (Polychromatic418967fa.accept_15_5_6_14_1_1721
  20 21 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 21 164 (accept_3_2 19
  21 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 21 164
  (Polychromatic418967fa.accept_12_6_9_8_1_165 18 21 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 21 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 21 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 21 164 (accept_3_2 16 21 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 21 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 21 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 21 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 14
  21 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 21 164 (accept_3_2 13 21
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 21 164
  (Polychromatic418967fa.accept_16_12_5_4_1_3275 12 21 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 21 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 21 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 21 164 (accept_3_2 10 21 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 21 164 (Polychromatic418967fa.accept_8_1_5_4_1_388 9 21 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 21 164 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  21 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 21 164 (accept_3_2 7 21 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 21 164 (Polychromatic418967fa.accept_9_6_3_2_1_431 6
  21 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 21 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 21 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 21 164 (accept_3_2 4 21 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 21
  164 (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 21 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 21 164 (Polychromatic418967fa.accept_22_2_21_10_1_9088 2 21 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 21 164 (accept_3_2 1 21 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 21 164))))))))))))))))))))) (allB_succ 20 164 (allA_succ_of_accept 19 20 164
  (accept_3_2 19 20 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 20 164 2 9 10 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 20 164
  (Polychromatic418967fa.accept_14_3_6_10_1_752 17 20 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 20 164 4 4 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 20 164 (Polychromatic418967fa.accept_13_2_7_8_1_4221 15 20 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 20 164 2 7 10 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 20 164 (accept_3_2 13 20 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 20 164 4 3 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 20 164 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 20 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 20 164 2 5 10 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 20 164 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 20
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 20 164 4 2 5 41 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 20 164 (accept_3_2 7 20
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 20 164 2 3 10 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 20 164
  (Polychromatic418967fa.accept_19_5_1_12_1_6102 5 20 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 20 164 4 1 5 41 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 20 164 (Polychromatic418967fa.accept_13_3_7_8_1_4192 3 20 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 20 164 2 1 10 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 20 164 (accept_3_2 1 20 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 20 164)))))))))))))))))))) (allB_succ 19 164 (allA_of_3_0 19 19 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 18 164 (allA_succ_of_accept 17 18 164 (Polychromatic418967fa.accept_15_2_3_14_1_972 17 18 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 18 164 2 8 9 82 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 18 164
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 18 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 18 164 2 7 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 18 164 (accept_3_2 13 18 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 18
  164 2 6 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  18 164 (Polychromatic418967fa.accept_15_11_3_14_1_971 11 18 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 18 164 2 5 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 18 164 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 18 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 18 164 2 4 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 18 164 (accept_3_2 7 18 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 18 164 2 3 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 18 164 (Polychromatic418967fa.accept_27_5_18_2_1_9087 5 18 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 18 164 2 2 9 82 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 18 164
  (Polychromatic418967fa.accept_11_3_7_10_1_180 3 18 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 18 164 2 1 9 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 18 164 (accept_3_2 1 18 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 18
  164)))))))))))))))))) (allB_succ 17 164 (allA_succ_of_accept 16 17 164 (accept_3_2 16 17 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 17 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 17 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 17 164
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 17 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 17 164 (accept_3_2 13 17 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  17 164 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 17 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 17 164 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 17 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 17 164 (accept_3_2 10 17 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 17 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 17 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 17 164
  (Polychromatic418967fa.accept_16_8_1_4_1_6622 8 17 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 17 164 (accept_3_2 7 17 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 17
  164 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 17 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 17 164 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 17 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 17 164 (accept_3_2 4 17 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 17 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 17 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 17 164 (Polychromatic418967fa.accept_10_2_7_4_1_967 2
  17 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 17 164 (accept_3_2 1 17 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 17 164))))))))))))))))) (allB_succ 16 164 (allA_of_3_0 16 16 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 15 164 (allA_succ_of_accept 14 15 164
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 15 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 15 164 (accept_3_2 13 15 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12
  15 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 15 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 15 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 15 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 15 164 (accept_3_2 10 15 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 15 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 15 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 15 164
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 15 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 15 164 (accept_3_2 7 15 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 15
  164 (Polychromatic418967fa.accept_10_6_5_4_1_571 6 15 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 15 164 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 15 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 15 164 (accept_3_2 4 15 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 15 164 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 15 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 15 164 (Polychromatic418967fa.accept_7_2_1_3_1_102 2
  15 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 15 164 (accept_3_2 1 15 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 15 164))))))))))))))) (allB_succ 14 164 (allA_succ_of_accept 13 14
  164 (accept_3_2 13 14 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 14 164 2 6 7 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 14 164
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 14 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 14 164 2 5 7 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 14 164 (Polychromatic418967fa.accept_13_9_1_8_1_1742 9 14 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 14 164 2 4 7 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 14 164 (accept_3_2 7 14 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 14 164 2 3 7 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 14 164 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 14 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 14 164 2 2 7 82 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 14 164 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 14
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 14 164 2 1 7 82 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 14 164 (accept_3_2 1 14
  164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 14 164)))))))))))))) (allB_succ 13 164 (allA_of_3_0 13 13 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 12 164 (allA_succ_of_accept 11 12 164
  (Polychromatic418967fa.accept_15_11_12_14_1_2612 11 12 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 12 164 2 5 6 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 12 164 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 12 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 12 164 4 2 3 41 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 12 164 (accept_3_2 7 12 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 6 12 164 2 3 6 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 5 12 164 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 12 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 12 164 4 1 3 41 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 12 164
  (Polychromatic418967fa.accept_16_3_12_4_1_170 3 12 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 12 164 2 1 6 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 12 164 (accept_3_2 1 12 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 12
  164)))))))))))) (allB_succ 11 164 (allA_succ_of_accept 10 11 164 (accept_3_2 10 11 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 11 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 11 164 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 11 164 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 11
  164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 11 164 (accept_3_2 7 11 164
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 11 164 (Polychromatic418967fa.accept_7_6_4_3_1_266 6
  11 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 11 164
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 5 11 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 11 164 (accept_3_2 4 11 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 11
  164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 11 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 11 164 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 11 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 11 164 (accept_3_2 1 11 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 11 164))))))))))) (allB_succ 10 164 (allA_of_3_0 10 10 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ 9 164 (allA_succ_of_accept 8 9 164 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 9 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 9 164 (accept_3_2 7 9 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 9 164 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 9 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 9 164
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 9 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 9 164 (accept_3_2 4 9 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 9 164
  (Polychromatic418967fa.accept_10_3_9_4_1_960 3 9 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 9 164 (Polychromatic418967fa.accept_17_2_9_11_1_4057 2 9 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 9 164 (accept_3_2 1 9 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 9 164))))))))) (allB_succ 8 164 (allA_succ_of_accept 7 8 164 (accept_3_2 7 8 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 8 164 2 3 4 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 8 164 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 8 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 8 164 4 1 2 41 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 8 164
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 8 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 8 164 2 1 4 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 8 164 (accept_3_2 1 8 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 8 164))))))))
  (allB_succ 7 164 (allA_of_3_0 7 7 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 6 164 (allA_succ_of_accept 5
  6 164 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 6 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 6 164 2 2 3 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 6 164 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 6 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 6 164 2 1 3 82 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 6 164 (accept_3_2 1 6 164 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 6 164)))))) (allB_succ 5 164 (allA_succ_of_accept 4 5 164 (accept_3_2 4 5 164 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 5 164 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 5 164
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 5 164
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 5 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 5 164 (accept_3_2 1 5 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 5 164)))))
  (allB_succ 4 164 (allA_of_3_0 4 4 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 3 164 (allA_succ_of_accept 2
  3 164 (Polychromatic418967fa.accept_15_2_3_14_1_972 2 3 164 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 3 164 (accept_3_2 1 3 164 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 3
  164))) (allB_succ 2 164 (allA_succ_of_accept 1 2 164 (accept_3_2 1 2 164 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 2 164)) (allB_two
  164))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


