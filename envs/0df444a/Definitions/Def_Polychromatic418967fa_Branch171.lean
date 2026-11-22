-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch171
-- name    : Polychromatic418967fa_Branch171
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:17:37.046979+00:00
-- url     : https://prove2.me/theorems/9aa8c5f9-eea6-404d-b05b-4a273829660c
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch171_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_171 : allB 171 171 :=
  allB_succ' 2 170 171 (Eq.refl Bool.true) (allA_succ_of_accept 1 170 171 (accept_3_4 1 170 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 170 171)) (allB_succ' 3 169 171 (Eq.refl Bool.true) (allA_succ_of_accept 2 169 171
  (accept_3_5 2 169 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 171
  (Polychromatic418967fa.accept_32_1_9_11_1_9712 1 169 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 169 171))) (allB_succ' 4 168 171 (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 171 3 1 56 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 171
  (Polychromatic418967fa.accept_18_2_6_9_1_1032 2 168 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 171 (Polychromatic418967fa.accept_13_1_12_2_1_384 1 168 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 171)))) (allB_succ' 5 167 171 (Eq.refl Bool.true) (allA_succ_of_accept 4
  167 171 (accept_3_4 4 167 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 171
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 167 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 167 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 167 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 171 (accept_3_4 1 167 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 167 171))))) (allB_succ' 6 166 171 (Eq.refl Bool.true) (allA_succ_of_accept 5 166 171
  (accept_3_5 5 166 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 171
  (Polychromatic418967fa.accept_16_4_6_11_1_3753 4 166 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 166 171 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 166 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 171 (accept_3_5 2 166 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 166 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 171)))))) (allB_succ' 7 165 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 165 171 3 2 55 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 165 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 165 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 165 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 171 3 1 55 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 165 171))))))) (allB_succ' 8 164 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 171 (accept_3_4 7 164 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  164 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 164 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 164 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 171 (accept_3_4 4 164 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 171 (Polychromatic418967fa.accept_18_3_2_9_1_1013 3 164 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 164 171
  (Polychromatic418967fa.accept_21_2_17_3_1_9644 2 164 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 164 171 (accept_3_4 1 164 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164
  171)))))))) (allB_succ' 9 163 171 (Eq.refl Bool.true) (allA_succ_of_accept 8 163 171 (accept_3_5 8 163 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 171 (Polychromatic418967fa.accept_15_7_13_6_1_696 7 163 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 171 (accept_3_5 5 163 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 163 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 171 (accept_3_5 2 163 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 171))))))))) (allB_succ' 10 162 171 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 162 171 9 1 18 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 162 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 162 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 162 171 (Polychromatic418967fa.accept_15_7_12_6_1_1327
  7 162 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 171 3 2 54 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 162 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 162 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 162 171 3 1 54 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 162 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 162 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 162 171)))))))))) (allB_succ' 11 161 171 (Eq.refl Bool.true) (allA_succ_of_accept 10 161 171 (accept_3_4 10
  161 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 171
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 161 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 161 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 161 171 (accept_3_4 7 161 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 161 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 161 171 (Polychromatic418967fa.accept_15_5_11_6_1_692
  5 161 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 171 (accept_3_4 4
  161 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 171
  (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 161 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 161 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 161 171 (accept_3_4 1 161 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 161 171))))))))))) (allB_succ' 12 160 171 (Eq.refl Bool.true) (allA_succ_of_accept 11 160 171
  (accept_3_5 11 160 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 160 171
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 160 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 160 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 160 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 171 (accept_3_5 8 160 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 160 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  160 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 160 171 (accept_3_5 5 160
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 160 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 160 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 160 171 (Polychromatic418967fa.accept_15_3_10_6_1_632 3 160 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 160 171 (accept_3_5 2 160 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 160 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 160 171)))))))))))) (allB_succ' 13 159 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 159 171 3 4 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 159 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 159 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 159
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 171 3 3 53 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 159 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 171 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 159 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 171 3 2 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 159 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 171
  (Polychromatic418967fa.accept_8_4_7_3_1_144 4 159 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 159 171 3 1 53 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 159 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 159 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 159 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159 171))))))))))))) (allB_succ' 14 158 171
  (Eq.refl Bool.true) (allA_succ_of_accept 13 158 171 (accept_3_4 13 158 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 158 171 (Polychromatic418967fa.accept_21_12_11_3_1_1052 12 158 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  158 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 171 (accept_3_4 10
  158 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 158 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 158 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 171 (accept_3_4 7 158 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 158 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 158 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  158 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 171 (accept_3_4 4 158
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 171
  (Polychromatic418967fa.accept_10_3_8_1_1_182 3 158 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 158 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 158 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 171 (accept_3_4 1 158 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 158 171)))))))))))))) (allB_succ' 15 157 171 (Eq.refl Bool.true) (allA_succ_of_accept 14 157 171
  (accept_3_5 14 157 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 171
  (Polychromatic418967fa.accept_15_13_7_6_1_682 13 157 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 157 171 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 157 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 171 (accept_3_5 11 157 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 157 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 9
  157 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 171 (accept_3_5 8 157
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 171
  (Polychromatic418967fa.accept_21_7_10_3_1_1049 7 157 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 157 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 171 (accept_3_5 5 157 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 157 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 171 (Polychromatic418967fa.accept_13_3_1_2_1_2960
  3 157 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 171 (accept_3_5 2
  157 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 171
  (Polychromatic418967fa.accept_15_1_7_6_1_6127 1 157 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 157 171))))))))))))))) (allB_succ' 16 156 171 (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 171 3 5 52 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 156 171
  (Polychromatic418967fa.accept_21_14_9_3_1_4893 14 156 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 156 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 156 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 171 3 4 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 171 (Polychromatic418967fa.accept_18_11_12_9_1_992
  11 156 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 171
  (Polychromatic418967fa.accept_16_10_12_11_1_346 10 156 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 156 171 3 3 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 156 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 156 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 7
  156 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 171 3 2 52 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 156 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 156 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 171 3 1 52 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 156 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 156 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 171)))))))))))))))) (allB_succ' 17 155 171 (Eq.refl Bool.true) (allA_succ_of_accept 16 155 171
  (accept_3_4 16 155 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 171
  (Polychromatic418967fa.accept_18_15_11_9_1_4256 15 155 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 155 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 171 (accept_3_4 13 155 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 155 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 155 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 171 (accept_3_4 10 155 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 155 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 171 (accept_3_4 7 155 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 6 155 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 155 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 171 (accept_3_4 4 155 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 171 (Polychromatic418967fa.accept_13_3_12_2_1_385 3 155 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 155 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 171 (accept_3_4 1 155 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 171))))))))))))))))) (allB_succ' 18 154 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 154 171 (accept_3_5 17 154 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 154 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 154 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 171 (accept_3_5 14 154 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 171
  (Polychromatic418967fa.accept_16_12_10_11_1_2667 12 154 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 154 171 (accept_3_5 11 154 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 154 171 (Polychromatic418967fa.accept_13_10_11_2_1_3862 10 154 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  154 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 171 (accept_3_5 8 154
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 171 (Polychromatic418967fa.accept_6_1_4_3_1_14
  7 154 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 154 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 171 (accept_3_5 5 154 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 171 (Polychromatic418967fa.accept_13_4_11_2_1_1458 4 154 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 154 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 171 (accept_3_5 2 154 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 171)))))))))))))))))) (allB_succ' 19 153
  171 (Eq.refl Bool.true) (allA_succ_of_gcd 18 153 171 9 2 17 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 153 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 153 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 153 171 3 5 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 153 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 153
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 171 3 4 51 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 153 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 171 9 1 17 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 153 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 153 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 153 171 3 2 51 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 5 153 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 153 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 171 3 1 51 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 153 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 171))))))))))))))))))) (allB_succ' 20 152 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 19 152 171 19 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 18 152 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 152 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 152 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 152 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 171 (accept_3_4 16 152 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 171 (Polychromatic418967fa.accept_7_1_5_3_1_268
  15 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 171 (accept_3_4 13 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 171 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 171 (accept_3_4 10 152 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 152 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 171 (accept_3_4 7 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 171 (accept_3_4 4 152 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 152 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 171 (accept_3_4 1 152 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  171)))))))))))))))))))) (allB_succ' 21 151 171 (Eq.refl Bool.true) (allA_succ_of_accept 20 151 171 (accept_3_5 20 151
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 171
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 151 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 151 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 18 151 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 171 (accept_3_5 17 151 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 151 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  151 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 171 (accept_3_5 14
  151 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 151 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 151 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 151 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 171 (accept_3_5 11 151 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 151 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 151 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  9 151 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 171 (accept_3_5 8
  151 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 171
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 151 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 151 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 171 (accept_3_5 5 151 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 151 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 3
  151 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 171 (accept_3_5 2 151
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 171 (Polychromatic418967fa.accept_7_1_4_3_1_21
  1 151 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 171)))))))))))))))))))))
  (allB_succ' 22 150 171 (Eq.refl Bool.true) (allA_succ_of_gcd 21 150 171 3 7 50 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 150 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 150 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 150 171 (Polychromatic418967fa.accept_16_3_6_11_1_2718 19 150 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 171 3 6 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  150 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 150 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 150 171 3 5 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 150 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 150 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 171 3 4 50 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 171
  (Polychromatic418967fa.accept_22_11_18_17_1_9711 11 150 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 150 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 150 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 150 171 3 3 50 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 150 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 150 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 150 171 (Polychromatic418967fa.accept_14_7_10_3_1_1034 7 150 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 171 3 2 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 150 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 150 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 150 171 3 1 50 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 150 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 150 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 171)))))))))))))))))))))) (allB_succ' 23
  149 171 (Eq.refl Bool.true) (allA_succ_of_accept 22 149 171 (accept_3_4 22 149 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 149 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 149 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 171 (accept_3_4 19 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 171 (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 149 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 171 (accept_3_4 16 149 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 149 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 171 (accept_3_4 13 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 171 (Polychromatic418967fa.accept_25_11_24_21_1_4074 11 149 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 171 (accept_3_4 10 149 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 149 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 171 (accept_3_4 7 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 171 (accept_3_4 4 149 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 171 (Polychromatic418967fa.accept_25_3_24_21_1_9710 3 149 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 171 (accept_3_4 1 149 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  171))))))))))))))))))))))) (allB_succ' 24 148 171 (Eq.refl Bool.true) (allA_succ_of_accept 23 148 171 (accept_3_5 23
  148 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 148 171
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 22 148 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 148 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 148 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 171 (accept_3_5 20 148 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 148 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 171 (Polychromatic418967fa.accept_7_4_1_3_1_277
  18 148 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 171 (accept_3_5 17
  148 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 148 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 148 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 148 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 171 (accept_3_5 14 148 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 148 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 171 (Polychromatic418967fa.accept_7_5_1_3_1_103
  12 148 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 171 (accept_3_5 11
  148 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 171
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 148 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 148 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 148 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 171 (accept_3_5 8 148 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 148 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 6
  148 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 171 (accept_3_5 5 148
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 148 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 148 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 148 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 171 (accept_3_5 2 148 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 148 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 171)))))))))))))))))))))))) (allB_succ' 25 147 171 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 147 171 3 8 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 147 171 (Polychromatic418967fa.accept_16_7_3_11_1_3682 23 147 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 171
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 147 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 147 171 3 7 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 147 171 (Polychromatic418967fa.accept_15_5_12_6_1_639 20 147 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 171 (Polychromatic418967fa.accept_13_6_4_2_1_1433 19 147
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 171 3 6 49 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 171
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 147 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 16 147 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 171 3 5 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 171 (Polychromatic418967fa.accept_10_4_7_1_1_471
  14 147 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 171
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 147 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 147 171 3 4 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 147 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 147 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 171 (Polychromatic418967fa.accept_14_10_7_3_1_1022 10 147
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 171 3 3 49 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 171
  (Polychromatic418967fa.accept_16_8_3_11_1_4763 8 147 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 171 (Polychromatic418967fa.accept_15_7_12_6_1_1327 7 147 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 171 3 2 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 171 (Polychromatic418967fa.accept_13_5_4_2_1_846 5 147 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 171
  (Polychromatic418967fa.accept_10_4_7_1_1_471 4 147 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 171 3 1 49 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 147 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 171 (Polychromatic418967fa.accept_18_1_3_9_1_328 1 147 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 171))))))))))))))))))))))))) (allB_succ' 26
  146 171 (Eq.refl Bool.true) (allA_succ_of_accept 25 146 171 (accept_3_4 25 146 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 146 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 146 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 146 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 146 171 (accept_3_4 22 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 146 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 146 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 20 146 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 146 171 (accept_3_4 19 146 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 146 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 146 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 146 171 (accept_3_4 16 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 146 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 146 171 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 146 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 171 (accept_3_4 13 146 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 146 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 146
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 146 171 (accept_3_4 10 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  146 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 146 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 8 146 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 171 (accept_3_4 7 146 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 146 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 146 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 146 171 (accept_3_4 4 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  146 171 (Polychromatic418967fa.accept_15_3_11_6_1_3083 3 146 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 146 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 146 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 171 (accept_3_4 1 146 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 146 171)))))))))))))))))))))))))) (allB_succ' 27 145 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 145 171 (accept_3_5 26 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 171 (Polychromatic418967fa.accept_17_8_9_1_1_3340 25 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 145 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 171 (accept_3_5 23 145 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 171
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 171 (accept_3_5 20 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 171 (accept_3_5 17 145 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 145 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 171 (accept_3_5 14 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 171 (Polychromatic418967fa.accept_25_13_20_21_1_9709 13 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 171 (Polychromatic418967fa.accept_14_12_5_3_1_1011 12 145 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 171 (accept_3_5 11 145 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10
  145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 171 (accept_3_5 8 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 171 (Polychromatic418967fa.accept_22_7_13_17_1_9708 7 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 171 (accept_3_5 5 145 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 171
  (Polychromatic418967fa.accept_15_3_10_6_1_632 3 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 171 (accept_3_5 2 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 171))))))))))))))))))))))))))) (allB_succ' 28 144 171 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 144 171 9 3 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 144 171 (Polychromatic418967fa.accept_15_11_9_6_1_1321 26 144 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 25 144
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 171 3 8 48 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 171
  (Polychromatic418967fa.accept_21_2_18_3_1_9697 23 144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 144 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 144 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 144 171 3 7 48 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 144 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 144 171
  (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 171 9 2 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 17 144 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 16 144
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 144 171 3 5 48 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 144 171
  (Polychromatic418967fa.accept_15_14_9_6_1_5093 14 144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 144 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 144 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 171 3 4 48 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 171 (Polychromatic418967fa.accept_15_11_9_6_1_1321
  11 144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 171
  (Polychromatic418967fa.accept_20_10_4_11_1_9652 10 144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 144 171 9 1 16 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 144 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 144 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319
  7 144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 171 3 2 48 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 171
  (Polychromatic418967fa.accept_10_5_4_1_1_842 5 144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 144 171 (Polychromatic418967fa.accept_15_4_9_6_1_627 4 144 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 144 171 3 1 48 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 144 171 (Polychromatic418967fa.accept_21_2_18_3_1_9697 2 144 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144 171)))))))))))))))))))))))))))) (allB_succ' 29 143 171 (Eq.refl Bool.true) (allA_succ_of_accept 28 143
  171 (accept_3_4 28 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 171
  (Polychromatic418967fa.accept_17_10_7_1_1_7024 27 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 143 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 143 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 171 (accept_3_4 25 143 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 143 171 (Polychromatic418967fa.accept_22_2_11_17_1_9707 24 143 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 171
  (Polychromatic418967fa.accept_16_7_15_11_1_951 23 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 171 (accept_3_4 22 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 143 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 171 (accept_3_4 19 143 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 143 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 143 171 (accept_3_4 16 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 143 171 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 143 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 171 (accept_3_4 13 143 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 143 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 171
  (Polychromatic418967fa.accept_17_11_7_1_1_7023 11 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 171 (accept_3_4 10 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 171 (accept_3_4 7 143 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 171 (Polychromatic418967fa.accept_22_6_11_17_1_9706 6 143 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 171
  (Polychromatic418967fa.accept_22_5_11_17_1_9705 5 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 171 (accept_3_4 4 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 171 (Polychromatic418967fa.accept_16_3_15_11_1_2676 3 143 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 143 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 171 (accept_3_4 1 143 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 171))))))))))))))))))))))))))))) (allB_succ' 30 142 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 142 171 (accept_3_5 29 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 171 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 142 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 171 (accept_3_5 26 142 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 171
  (Polychromatic418967fa.accept_26_24_12_15_1_9704 24 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 142 171 (accept_3_5 23 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 142 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 142 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 171 (accept_3_5 20 142 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 171 (accept_3_5 17 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 16 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 142 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 171 (accept_3_5 14 142 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 171 (accept_3_5 11 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 171 (Polychromatic418967fa.accept_13_10_12_2_1_1460 10 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 171 (accept_3_5 8 142 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 142 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 171 (accept_3_5 5 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 171 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 142 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 142 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 171 (accept_3_5 2 142 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 171)))))))))))))))))))))))))))))) (allB_succ' 31 141
  171 (Eq.refl Bool.true) (allA_succ_of_gcd 30 141 171 3 10 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 141 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 171
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 141 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 141 171 3 9 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 141 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 141 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 171 3 8 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 141 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 171 3 7 47 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 171
  (Polychromatic418967fa.accept_22_20_9_17_1_9703 20 141 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 141 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 141 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 171 3 6 47 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 17 141 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 141 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 171 3 5 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  141 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 141 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 141 171 3 4 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 141 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 141 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 171 3 3 47 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 171
  (Polychromatic418967fa.accept_16_8_13_11_1_4772 8 141 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 141 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 171 3 2 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 141 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 4 141 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 141 171 3 1 47 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 141 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 141 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141 171)))))))))))))))))))))))))))))))
  (allB_succ' 32 140 171 (Eq.refl Bool.true) (allA_succ_of_accept 31 140 171 (accept_3_4 31 140 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 140 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 140 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 140 171 (accept_3_4 28 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 140 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 140 171 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 140 171 (accept_3_4 25 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 140 171 (Polychromatic418967fa.accept_13_11_10_2_1_3840 24 140
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 140 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 140 171 (accept_3_4 22 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 140 171 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 140 171 (Polychromatic418967fa.accept_16_4_12_11_1_2650 20 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 140 171 (accept_3_4 19 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 140 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 171 (accept_3_4 16 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 140 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 140 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 14 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 171 (accept_3_4 13 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 140 171 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 140
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 140 171 (accept_3_4 10 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  140 171 (Polychromatic418967fa.accept_21_9_14_3_1_9678 9 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 140 171 (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 171 (accept_3_4 7 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 140 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 140 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 140 171 (accept_3_4 4 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  140 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 140 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 140 171 (Polychromatic418967fa.accept_21_2_14_3_1_4933 2 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 171 (accept_3_4 1 140 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 140 171)))))))))))))))))))))))))))))))) (allB_succ' 33 139 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 32 139 171 (accept_3_5 32 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 139 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 139 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 139 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 139 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 171 (accept_3_5 29 139 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28
  139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 171
  (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 171 (accept_3_5 26 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 171 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 139 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 171 (accept_3_5 23 139 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 139 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 171 (accept_3_5 20 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 171 (Polychromatic418967fa.accept_13_6_9_2_1_838 19 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 139 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 171 (accept_3_5 17 139 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 15 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 171 (accept_3_5 14 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 171 (Polychromatic418967fa.accept_15_13_4_6_1_3046 13 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 139 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 171 (accept_3_5 11 139 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 139 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 171 (accept_3_5 8 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 171 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 171 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 139 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 171 (accept_3_5 5 139 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 171
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 171 (accept_3_5 2 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 1 139 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 171))))))))))))))))))))))))))))))))) (allB_succ' 34 138 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 138 171 3 11 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 138 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 138 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 138 171 (Polychromatic418967fa.accept_15_1_3_6_1_621
  31 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 138 171 3 10 46 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 138 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 138 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 138 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 138 171 3 9 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 138 171 (Polychromatic418967fa.accept_12_2_6_3_1_331
  26 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 171 3 8 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 138 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 138 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 138 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 138 171 3 7 46 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 138 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 138 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 138 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 138 171 3 6 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 138 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 138 171 3 5 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 138 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 138 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 138 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 171 3 4 46 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 171
  (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 138 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 138 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 138 171 3 3 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 138 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 138 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 171
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 171 3 2 46 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 138 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 138 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 138 171 3 1 46 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 138 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 138 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 138 171)))))))))))))))))))))))))))))))))) (allB_succ' 35 137 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 34 137 171 (accept_3_4 34 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 137 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 137 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 137 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 171 (accept_3_4 31 137 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 171 (accept_3_4 28 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 171 (accept_3_4 25 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 137 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 171
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 171 (accept_3_4 22 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 171 (accept_3_4 19 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 171
  (Polychromatic418967fa.accept_27_17_2_9_1_5565 17 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 171 (accept_3_4 16 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 171 (accept_3_4 13 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 137 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 171
  (Polychromatic418967fa.accept_15_11_2_6_1_3010 11 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 171 (accept_3_4 10 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 171 (accept_3_4 7 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 171
  (Polychromatic418967fa.accept_13_5_7_2_1_852 5 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 171 (accept_3_4 4 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 171 (Polychromatic418967fa.accept_22_3_5_17_1_9702 3 137 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 171 (accept_3_4 1 137 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 171))))))))))))))))))))))))))))))))))) (allB_succ' 36 136 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 136 171 (accept_3_5 35 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 171 (Polychromatic418967fa.accept_13_8_6_2_1_865 34 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 33 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 171 (accept_3_5 32 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 136 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 171 (accept_3_5 29 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 171 (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 171 (accept_3_5 26 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 136 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 171
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 171 (accept_3_5 23 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 171 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 171 (accept_3_5 20 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 171 (accept_3_5 17 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 171 (Polychromatic418967fa.accept_21_16_10_3_1_9671 16 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 171 (accept_3_5 14 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 171 (accept_3_5 11 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 171 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 136 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 171 (accept_3_5 8 136 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 171
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 171 (accept_3_5 5 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 171 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 136 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 136 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 171 (accept_3_5 2 136 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 171)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 135 171 (Eq.refl Bool.true) (allA_succ_of_gcd 36 135 171 9 4 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 135 171 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 135
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 34 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 135 171 3 11 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 135 171 (Polychromatic418967fa.accept_17_15_16_1_1_7080 32 135 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 171
  (Polychromatic418967fa.accept_11_9_3_6_1_797 31 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 135 171 3 10 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 135 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 135 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 171 (Polychromatic418967fa.accept_8_4_7_3_1_144
  28 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 135 171 9 3 15 19
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 135 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 171 (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 135 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 171 3 8 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 171 (Polychromatic418967fa.accept_13_10_5_2_1_1477
  23 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 135 171 3 7 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 135 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 135 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 135 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 171 9 2 15 19 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 171
  (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 16 135 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 171 3 5 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 171 (Polychromatic418967fa.accept_10_4_5_1_1_497
  14 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 135 171 3 4 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 135 171 (Polychromatic418967fa.accept_23_11_20_10_1_9664 11 135 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 171
  (Polychromatic418967fa.accept_13_10_5_2_1_1477 10 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 135 171 9 1 15 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 135 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 171 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 135 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 171 3 2 45 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 135 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 171 3 1 45 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 171 (Polychromatic418967fa.accept_16_2_7_11_1_1698 2 135 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 135 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135 171))))))))))))))))))))))))))))))))))))) (allB_succ' 38 134 171 (Eq.refl Bool.true) (allA_succ_of_accept
  37 134 171 (accept_3_4 37 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 134 171
  (Polychromatic418967fa.accept_16_4_6_11_1_3753 36 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 134 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 134 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 171 (accept_3_4 34 134 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 134 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 171 (Polychromatic418967fa.accept_7_4_1_3_1_277
  32 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 171 (accept_3_4 31
  134 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 134 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 171 (accept_3_4 28 134 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 134 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 134 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 171 (accept_3_4 25 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 171 (accept_3_4 22 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 171
  (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 171 (accept_3_4 19 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 171 (accept_3_4 16 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 134 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 171
  (Polychromatic418967fa.accept_21_14_8_3_1_8085 14 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 171 (accept_3_4 13 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 171 (accept_3_4 10 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 171
  (Polychromatic418967fa.accept_15_8_14_6_1_3003 8 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 171 (accept_3_4 7 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 171 (accept_3_4 4 134 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 171 (Polychromatic418967fa.accept_16_3_6_11_1_2718 3 134 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 171 (accept_3_4 1 134 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  171)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 133 171 (Eq.refl Bool.true) (allA_succ_of_gcd 38 133 171 19 2
  7 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 133 171
  (Polychromatic418967fa.accept_13_11_3_2_1_863 37 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 133 171 (Polychromatic418967fa.accept_13_10_3_2_1_4728 36 133 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 171 (accept_3_5 35 133 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 133 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 171 (Polychromatic418967fa.accept_12_9_1_3_1_350
  33 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 171 (accept_3_5 32
  133 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 171
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 133 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 171 (accept_3_5 29 133 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 133 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 133 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 171 (Polychromatic418967fa.accept_11_5_1_6_1_774
  27 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 171 (accept_3_5 26
  133 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 171
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 25 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 133 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 24 133 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 171 (accept_3_5 23 133 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 133 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 171 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 171 (accept_3_5 20
  133 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 133 171 19 1 7 9 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 18 133 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 133 171 (accept_3_5 17 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 133 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 133 171 (Polychromatic418967fa.accept_20_15_13_11_1_5110 15 133 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 133 171 (accept_3_5 14 133 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 133 171 (Polychromatic418967fa.accept_17_13_14_1_1_2258 13 133
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 133 171
  (Polychromatic418967fa.accept_10_2_3_1_1_481 12 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 133 171 (accept_3_5 11 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 133 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 133 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 133 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 133 171 (accept_3_5 8 133 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 133 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 133 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 133 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 133 171 (accept_3_5 5 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  133 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 133 171 (Polychromatic418967fa.accept_18_3_7_9_1_5486 3 133 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 133 171 (accept_3_5 2 133 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 133 171 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 133 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 133 171)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 132 171 (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 171 3 13 44 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 132 171
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 132 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 132 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 171 3 12 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 171 (Polychromatic418967fa.accept_15_5_12_6_1_639
  35 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 171
  (Polychromatic418967fa.accept_21_13_6_3_1_3381 34 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 132 171 3 11 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 132 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 132 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 171 (Polychromatic418967fa.accept_8_7_4_3_1_156
  31 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 171 3 10 44 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 171
  (Polychromatic418967fa.accept_10_9_2_1_1_840 29 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 132 171 (Polychromatic418967fa.accept_16_12_4_11_1_3710 28 132 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 132 171 3 9 44 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 132 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 171 3 8 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 171
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 22 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 132 171 3 7 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 132 171 (Polychromatic418967fa.accept_15_5_12_6_1_639 20 132 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 171 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 132
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 171 3 6 44 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 171
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 17 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 132 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 132 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 132 171 3 5 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 132 171
  (Polychromatic418967fa.accept_17_14_13_1_1_3356 14 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 132 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 13 132 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 171 3 4 44 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 132 171 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 132 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 132 171 3 3 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 132 171 (Polychromatic418967fa.accept_16_8_4_11_1_2687 8 132 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 132 171
  (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 132 171 3 2 44 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 132 171 (Polychromatic418967fa.accept_15_5_12_6_1_639 5 132 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 132 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 132 171 3 1 44 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 132 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 132 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 132 171 (Polychromatic418967fa.accept_18_1_6_9_1_2001 1 132 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132 171)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 131 171
  (Eq.refl Bool.true) (allA_succ_of_accept 40 131 171 (accept_3_4 40 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 131 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 39 131 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 131 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 171 (accept_3_4 37 131 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 171 (Polychromatic418967fa.accept_7_1_5_3_1_268
  36 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 171
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 171 (accept_3_4 34 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 171 (accept_3_4 31 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 131 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 171 (accept_3_4 28 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 27 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 171 (accept_3_4 25 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 131 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 171 (accept_3_4 22 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 171 (accept_3_4 19 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 171 (Polychromatic418967fa.accept_15_3_11_6_1_3083 18 131 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 171
  (Polychromatic418967fa.accept_15_2_11_6_1_2135 17 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 171 (accept_3_4 16 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 171 (accept_3_4 13 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 171 (Polychromatic418967fa.accept_13_12_1_2_1_845 12 131 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 171
  (Polychromatic418967fa.accept_25_11_6_21_1_9701 11 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 131 171 (accept_3_4 10 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 131 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 131 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 171 (accept_3_4 7 131 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 171 (Polychromatic418967fa.accept_13_6_1_2_1_1464
  6 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 171
  (Polychromatic418967fa.accept_11_5_10_6_1_793 5 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 171 (accept_3_4 4 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 171 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 131 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 171 (accept_3_4 1 131 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 171))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 130 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 171 (accept_3_5 41 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 130 171 (Polychromatic418967fa.accept_22_18_20_17_1_9700 40 130 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 130 171 (Polychromatic418967fa.accept_16_7_2_11_1_931
  39 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 171 (accept_3_5 38
  130 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 130 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 130 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 130 171 (accept_3_5 35 130 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 130 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 130 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 171 (accept_3_5 32
  130 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 171
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 130 171 (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 130 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 130 171 (accept_3_5 29 130 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 130 171 (Polychromatic418967fa.accept_21_7_4_3_1_6424 28 130 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 130 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 130 171 (accept_3_5 26 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 130 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 130 171 (Polychromatic418967fa.accept_17_7_11_1_1_4503 24 130 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 171 (accept_3_5 23 130 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 130 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 130 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 130 171 (accept_3_5 20 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 130 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 130 171 (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 130 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 130 171 (accept_3_5 17 130 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 130 171 (Polychromatic418967fa.accept_15_1_10_6_1_631 16 130
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 130 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 15 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 130 171 (accept_3_5 14 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 130 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 130 171 (Polychromatic418967fa.accept_15_12_10_6_1_2134 12 130 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 171 (accept_3_5 11 130 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 130 171 (Polychromatic418967fa.accept_17_10_11_1_1_5784 10 130
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 130 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 130 171 (accept_3_5 8 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  130 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 130 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 130 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 130 171 (accept_3_5 5 130 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 130 171 (Polychromatic418967fa.accept_15_4_10_6_1_2997 4 130 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 3 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 130 171 (accept_3_5 2 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  130 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 130 171)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 129 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 129 171 3 14 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 129 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 129 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 171 (Polychromatic418967fa.accept_13_1_12_2_1_384
  40 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 129 171 3 13 43 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 129 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 129 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 129 171 3 12 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 129 171 (Polychromatic418967fa.accept_10_5_9_1_1_187
  35 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 171 3 11 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 32 129 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 171 (Polychromatic418967fa.accept_12_7_9_3_1_767
  31 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 171 3 10 43 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 28 129 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 171 3 9 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 171
  (Polychromatic418967fa.accept_10_5_9_1_1_187 25 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 129 171 3 8 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 129 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 129 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 171 3 7 43 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 171
  (Polychromatic418967fa.accept_18_2_3_9_1_1996 20 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 129 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 171 3 6 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 171
  (Polychromatic418967fa.accept_13_3_12_2_1_385 16 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 129 171 3 5 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 129
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 171 3 4 43 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 171
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 171 3 3 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 8 129 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 129 171 3 2 43 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 129 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 129 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 171 (Polychromatic418967fa.accept_13_4_12_2_1_1459 4 129
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 171 3 1 43 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 129 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129 171))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 128 171
  (Eq.refl Bool.true) (allA_succ_of_accept 43 128 171 (accept_3_4 43 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 128 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 128 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 128 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 171 (accept_3_4 40 128 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  39 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 128 171
  (Polychromatic418967fa.accept_20_18_8_11_1_9699 38 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 128 171 (accept_3_4 37 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 128 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 128 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 128 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 128 171 (accept_3_4 34 128 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 128 171 (Polychromatic418967fa.accept_7_5_2_3_1_106
  33 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 128 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 32 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 128 171 (accept_3_4 31 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 128 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 128 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 128 171 (accept_3_4 28 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 128 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 128 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 128 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 128 171 (accept_3_4 25 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 128 171 (Polychromatic418967fa.accept_18_6_2_9_1_3056 24 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 128 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 128 171 (accept_3_4 22 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 128 171 (Polychromatic418967fa.accept_18_3_2_9_1_1013 21 128 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 128 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 128 171 (accept_3_4 19 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 128 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 128 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 128 171 (accept_3_4 16 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 128 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 128 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 128 171
  (Polychromatic418967fa.accept_15_14_8_6_1_2133 14 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 128 171 (accept_3_4 13 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 128 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 128 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 128 171 (accept_3_4 10 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 128 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 9 128 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 128 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 128 171 (accept_3_4 7 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  128 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 128 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 128 171 (accept_3_4 4 128 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 128 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 128 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 128 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 2 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 128 171 (accept_3_4 1 128 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  171)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 127 171 (Eq.refl Bool.true) (allA_succ_of_accept 44 127
  171 (accept_3_5 44 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 171
  (Polychromatic418967fa.accept_15_13_7_6_1_682 43 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 127 171 (Polychromatic418967fa.accept_13_3_10_2_1_381 42 127 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 171 (accept_3_5 41 127 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 127 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 171 (Polychromatic418967fa.accept_7_4_1_3_1_277
  39 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 171 (accept_3_5 38
  127 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 127 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 127 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 171 (accept_3_5 35 127 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 127 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 127 171 (Polychromatic418967fa.accept_7_5_1_3_1_103
  33 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 171 (accept_3_5 32
  127 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 171
  (Polychromatic418967fa.accept_13_5_10_2_1_856 31 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 127 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 127 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 171 (accept_3_5 29 127 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 127 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 127 171
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 127 171 (accept_3_5 26 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 127 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 127 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 127 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 171 (accept_3_5 23 127 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 127 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 127 171
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 127 171 (accept_3_5 20 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 127 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 127 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 171 (accept_3_5 17 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 171
  (Polychromatic418967fa.accept_21_15_1_3_1_9587 15 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 127 171 (accept_3_5 14 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 127 171 (Polychromatic418967fa.accept_15_13_7_6_1_682 13 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 127 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 171 (accept_3_5 11 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 127 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 127 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 127 171 (accept_3_5 8 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  127 171 (Polychromatic418967fa.accept_16_7_15_11_1_951 7 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 127 171 (Polychromatic418967fa.accept_10_6_7_1_1_1297 6 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 127 171 (accept_3_5 5 127 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 127 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 171
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 127 171 (accept_3_5 2 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  127 171 (Polychromatic418967fa.accept_15_1_7_6_1_6127 1 127 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 127 171))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 126 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 126 171 9 5 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 126 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 126
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 171 3 14 42 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 126 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 126 171 3 13 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 126 171 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 171 9 4 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 126 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 35 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 34 126
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 126 171 3 11 42 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 126 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 171 (Polychromatic418967fa.accept_13_5_9_2_1_1489 31 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 171 3 10 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 126 171 9 3 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 126 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 171 3 8 42 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 171
  (Polychromatic418967fa.accept_11_1_5_6_1_397 23 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 171 3 7 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 171 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 171
  (Polychromatic418967fa.accept_13_6_9_2_1_838 19 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 171 9 2 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 126
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 126 171 3 5 42 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 126 171
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 171 3 4 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 171 (Polychromatic418967fa.accept_13_11_9_2_1_2969
  11 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 171
  (Polychromatic418967fa.accept_11_10_5_6_1_1842 10 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 126 171 9 1 14 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 126 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 7 126 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 171 3 2 42 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 126 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 171 3 1 42 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 126 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 171)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 125 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 125 171 (accept_3_4 46 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 171 (accept_3_4 43 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 171
  (Polychromatic418967fa.accept_15_11_5_6_1_669 41 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 171 (accept_3_4 40 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 171 (accept_3_4 37 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 36 125 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 171
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 35 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 171 (accept_3_4 34 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 171 (accept_3_4 31 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 171
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 171 (accept_3_4 28 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 171 (Polychromatic418967fa.accept_15_12_5_6_1_2148 27 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 171 (accept_3_4 25 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 24 125 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 171 (accept_3_4 22 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 171 (accept_3_4 19 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 171
  (Polychromatic418967fa.accept_20_17_5_11_1_9622 17 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 125 171 (accept_3_4 16 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 125 171 (Polychromatic418967fa.accept_18_15_17_9_1_4200 15 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 171 (accept_3_4 13
  125 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 171
  (Polychromatic418967fa.accept_15_12_5_6_1_2148 12 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 125 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 125 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 171 (accept_3_4 10 125 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 125 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8
  125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 171 (accept_3_4 7 125
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 171 (Polychromatic418967fa.accept_4_2_1_3_1_27
  6 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 171
  (Polychromatic418967fa.accept_17_5_6_1_1_5735 5 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 171 (accept_3_4 4 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 171 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3 125 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 171 (accept_3_4 1 125 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 171))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 124 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 171 (accept_3_5 47 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 124 171 (Polychromatic418967fa.accept_27_19_16_9_1_9698 46 124 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 171 (Polychromatic418967fa.accept_10_5_4_1_1_842
  45 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 171 (accept_3_5 44
  124 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 171
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 124 171 (Polychromatic418967fa.accept_11_9_3_6_1_797 42 124 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 171 (accept_3_5 41 124 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 124 171 (Polychromatic418967fa.accept_15_10_4_6_1_2129 40 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 171
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 124 171 (accept_3_5 38 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 124 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 124 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 124 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 171 (accept_3_5 35 124 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 124 171 (Polychromatic418967fa.accept_13_8_7_2_1_2988 34 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 171
  (Polychromatic418967fa.accept_14_5_12_3_1_3397 33 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 124 171 (accept_3_5 32 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 124 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 124 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 124 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 171 (accept_3_5 29 124 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 124 171 (Polychromatic418967fa.accept_15_13_4_6_1_3046 28 124 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 171
  (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 124 171 (accept_3_5 26 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 124 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 124 171 (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 171 (accept_3_5 23 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 124 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 124 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 171
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 171 (accept_3_5 20 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 171 (accept_3_5 17 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 124 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 171 (accept_3_5 14 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 171 (Polychromatic418967fa.accept_18_12_16_9_1_4198 12 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 171 (accept_3_5 11 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 171 (Polychromatic418967fa.accept_15_10_4_6_1_2129 10 124
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 171 (accept_3_5 8 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 124 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 171 (accept_3_5 5 124 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 171 (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 124 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 171
  (Polychromatic418967fa.accept_22_3_14_17_1_3159 3 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 171 (accept_3_5 2 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 171)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 123 171 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 123 171 3 16 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 123 171 (Polychromatic418967fa.accept_13_8_6_2_1_865 47 123 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 171
  (Polychromatic418967fa.accept_15_1_3_6_1_621 46 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 123 171 3 15 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 123 171 (Polychromatic418967fa.accept_21_2_18_3_1_9697 44 123 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 171 3 14 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 123 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 171 (Polychromatic418967fa.accept_13_1_6_2_1_377
  40 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 171 3 13 41 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 171
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 38 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 37 123 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 171 3 12 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200
  35 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 171 3 11 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 32 123 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 171 (Polychromatic418967fa.accept_15_1_3_6_1_621
  31 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 123 171 3 10 41 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 123 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 28 123 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 171 3 9 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 171 (Polychromatic418967fa.accept_11_4_2_6_1_389
  26 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 171
  (Polychromatic418967fa.accept_13_12_6_2_1_1441 25 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 123 171 3 8 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 123 171 (Polychromatic418967fa.accept_13_10_6_2_1_1440 23 123 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 123 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 171 3 7 41 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 171 (Polychromatic418967fa.accept_21_19_18_3_1_4910 19 123 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 171 3 6 41 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 171
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 171 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 123 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 171 3 5 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 171 (Polychromatic418967fa.accept_13_1_6_2_1_377
  14 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 171 3 4 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 171 (Polychromatic418967fa.accept_15_11_3_6_1_1306 11 123 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 171 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 123
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 171 3 3 41 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 171 (Polychromatic418967fa.accept_14_7_11_3_1_5365 7 123 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 171 3 2 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 171 (Polychromatic418967fa.accept_15_5_3_6_1_2128 5 123 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 171
  (Polychromatic418967fa.accept_11_4_2_6_1_389 4 123 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 171 3 1 41 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 171 (Polychromatic418967fa.accept_10_2_3_1_1_481 2 123 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 123 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  171))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 122 171 (Eq.refl Bool.true) (allA_succ_of_accept
  49 122 171 (accept_3_4 49 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 122 171
  (Polychromatic418967fa.accept_13_9_5_2_1_2185 48 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 122 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 122 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 171 (accept_3_4 46 122 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 122 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 171
  (Polychromatic418967fa.accept_16_12_10_11_1_2667 44 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 122 171 (accept_3_4 43 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 122 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 122 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 122 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 171 (accept_3_4 40 122 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 171 (Polychromatic418967fa.accept_10_9_2_1_1_840
  39 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 171
  (Polychromatic418967fa.accept_11_5_1_6_1_774 38 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 171 (accept_3_4 37 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 171 (accept_3_4 34 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 171
  (Polychromatic418967fa.accept_17_15_3_1_1_9696 32 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 171 (accept_3_4 31 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 171 (accept_3_4 28 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 27 122 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 26 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 171 (accept_3_4 25 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 171 (Polychromatic418967fa.accept_18_6_14_9_1_3039 24 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 171 (accept_3_4 22 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 171
  (Polychromatic418967fa.accept_13_7_5_2_1_401 20 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 171 (accept_3_4 19 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 18 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 171 (accept_3_4 16 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 171 (Polychromatic418967fa.accept_16_15_10_11_1_1727 15 122 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 171
  (Polychromatic418967fa.accept_21_14_17_3_1_9695 14 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 122 171 (accept_3_4 13 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 122 171 (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 122 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 122 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 171 (accept_3_4 10 122 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 171
  (Polychromatic418967fa.accept_15_8_2_6_1_2125 8 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 171 (accept_3_4 7 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 6 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 171 (accept_3_4 4 122 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 122 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 171
  (Polychromatic418967fa.accept_17_2_3_1_1_2244 2 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 171 (accept_3_4 1 122 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  171)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 121 171 (Eq.refl Bool.true) (allA_succ_of_accept
  50 121 171 (accept_3_5 50 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 171
  (Polychromatic418967fa.accept_21_7_16_3_1_1058 49 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 121 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 171 (accept_3_5 47 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 121 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 171 (Polychromatic418967fa.accept_12_9_1_3_1_350
  45 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 171 (accept_3_5 44
  121 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 121 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 171 (accept_3_5 41 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 121 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 121 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 171 (Polychromatic418967fa.accept_15_9_1_6_1_657
  39 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 171 (accept_3_5 38
  121 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 171
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 121 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 171 (accept_3_5 35 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 121 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 171 (Polychromatic418967fa.accept_7_5_2_3_1_106
  33 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 171 (accept_3_5 32
  121 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 171
  (Polychromatic418967fa.accept_13_5_4_2_1_846 31 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 121 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 171 (accept_3_5 29 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 121 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 171 (Polychromatic418967fa.accept_7_6_2_3_1_107
  27 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 171 (accept_3_5 26
  121 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 171
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 25 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 121 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 171 (accept_3_5 23 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 121 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 171 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 171 (accept_3_5 20
  121 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 121 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 171 (accept_3_5 17 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 121 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 171 (Polychromatic418967fa.accept_7_1_2_3_1_257
  15 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 171 (accept_3_5 14
  121 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 171
  (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 121 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 171 (accept_3_5 11 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 121 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 9
  121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 171 (accept_3_5 8 121
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 171
  (Polychromatic418967fa.accept_15_7_1_6_1_6150 7 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 121 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 171 (accept_3_5 5 121 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 121 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 3
  121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 171 (accept_3_5 2 121
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 121 171))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 120 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 51 120 171 3 17 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 120 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 50 120 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 171
  (Polychromatic418967fa.accept_11_5_10_6_1_793 49 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 171 3 16 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 120 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 171 (Polychromatic418967fa.accept_7_4_1_3_1_277
  46 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 120 171 3 15 40 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 120 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 44 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 171 (Polychromatic418967fa.accept_21_1_15_3_1_4817 43 120 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 171 3 14 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 171 (Polychromatic418967fa.accept_18_5_12_9_1_6871
  41 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 40 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 120 171 3 13 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 120 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 38 120 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 171 3 12 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 171 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 120 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 171
  (Polychromatic418967fa.accept_18_16_12_9_1_5504 34 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 120 171 3 11 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 120 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 120 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 171
  (Polychromatic418967fa.accept_13_5_3_2_1_1499 31 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 171 3 10 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 171 (Polychromatic418967fa.accept_16_13_8_11_1_4785 29 120 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 171
  (Polychromatic418967fa.accept_16_12_8_11_1_2695 28 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 120 171 3 9 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 120 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 120 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 171 3 8 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 171 (Polychromatic418967fa.accept_13_9_3_2_1_399 22 120
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 171 3 7 40 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 120 171
  (Polychromatic418967fa.accept_16_4_8_11_1_5961 20 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 120 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 171 3 6 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 171
  (Polychromatic418967fa.accept_18_17_12_9_1_3031 17 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 120 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 120 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 120 171 3 5 40 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 120 171
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 120 171 (Polychromatic418967fa.accept_16_13_8_11_1_4785 13 120 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 171 3 4 40 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 171 (Polychromatic418967fa.accept_13_10_3_2_1_4728 10 120 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 120 171 3 3 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 120 171 (Polychromatic418967fa.accept_21_8_15_3_1_279 8 120 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 171
  (Polychromatic418967fa.accept_21_7_15_3_1_8029 7 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 171 3 2 40 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 120 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 120 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 171 3 1 40 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 120 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 171 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 120 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 171)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  119 171 (Eq.refl Bool.true) (allA_succ_of_accept 52 119 171 (accept_3_4 52 119 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 119 171 (Polychromatic418967fa.accept_16_3_7_11_1_1723 51 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 171 (accept_3_4 49 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 48 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 47 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 171 (accept_3_4 46 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 119
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 171 (accept_3_4 43 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 171 (Polychromatic418967fa.accept_10_2_9_1_1_185 42 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 171 (Polychromatic418967fa.accept_25_16_19_21_1_9694 41 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 171 (accept_3_4 40 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 171 (Polychromatic418967fa.accept_14_11_7_3_1_3416 39 119
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 171 (accept_3_4 37 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 35 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 171 (accept_3_4 34 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 119
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 171 (accept_3_4 31 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 171 (Polychromatic418967fa.accept_18_12_11_9_1_4257 30 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 171 (Polychromatic418967fa.accept_21_8_14_3_1_9602 29 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 171 (accept_3_4 28 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 171 (Polychromatic418967fa.accept_21_6_14_3_1_4932 27 119
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 171 (accept_3_4 25 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 171 (Polychromatic418967fa.accept_14_10_7_3_1_1022 24 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 171 (Polychromatic418967fa.accept_15_8_14_6_1_3003 23 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 171 (accept_3_4 22 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 119
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 171 (accept_3_4 19 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 171 (Polychromatic418967fa.accept_10_8_9_1_1_189 18 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 171 (Polychromatic418967fa.accept_21_17_14_3_1_6411 17 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 171 (accept_3_4 16 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 15 119
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 171 (accept_3_4 13 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 171 (Polychromatic418967fa.accept_14_11_7_3_1_3416 11 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 171 (accept_3_4 10 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 171 (accept_3_4 7 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 171 (Polychromatic418967fa.accept_21_6_14_3_1_4932 6 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 119 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 171 (accept_3_4 4 119 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 3 119 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 171 (accept_3_4 1 119 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  171))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 118 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 118 171 (accept_3_5 53 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 171 (Polychromatic418967fa.accept_14_10_6_3_1_1055 52 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 171 (accept_3_5 50 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 171
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 48 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 171 (accept_3_5 47 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 171 (accept_3_5 44 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 171 (accept_3_5 41 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 171 (Polychromatic418967fa.accept_23_17_3_10_1_4426 40 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 171 (accept_3_5 38 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 171
  (Polychromatic418967fa.accept_11_3_8_6_1_788 36 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 171 (accept_3_5 35 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 171 (Polychromatic418967fa.accept_15_4_13_6_1_642 34 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 171 (accept_3_5 32 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 30 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 171 (accept_3_5 29 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 171 (Polychromatic418967fa.accept_20_8_18_11_1_5133 28 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 171 (Polychromatic418967fa.accept_20_7_18_11_1_5080 27 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 171 (accept_3_5 26 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 171
  (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 171 (accept_3_5 23 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 171 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 171 (accept_3_5 20 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 18 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 171 (accept_3_5 17 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 171 (Polychromatic418967fa.accept_17_15_16_1_1_7080 15 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 171 (accept_3_5 14 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 171
  (Polychromatic418967fa.accept_13_12_1_2_1_845 12 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 171 (accept_3_5 11 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 171 (Polychromatic418967fa.accept_14_10_6_3_1_1055 10 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 171 (accept_3_5 8 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 171 (accept_3_5 5 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 118 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 171 (accept_3_5 2 118 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 117 171 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 117 171 9 6 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 117 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 171 (Polychromatic418967fa.accept_15_7_12_6_1_1327 52 117
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 171 3 17 39 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 171 3 16 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 171 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 171 9 5 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 117 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 117 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 171 3 14 39 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 171 (Polychromatic418967fa.accept_14_12_5_3_1_1011 40 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 171 3 13 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 171 9 4 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 117 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 171 3 11 39 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 171
  (Polychromatic418967fa.accept_15_2_12_6_1_3063 32 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 117 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 31 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 171 3 10 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 117 171
  (Polychromatic418967fa.accept_20_8_17_11_1_9604 28 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 117 171 9 3 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 117 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 117 171 3 8 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 117 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 171 3 7 39 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 171
  (Polychromatic418967fa.accept_15_5_12_6_1_639 20 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 171 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 171 9 2 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 117 171 3 5 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 117 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 117
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 171 3 4 39 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 171
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 117 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 171 9 1 13 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 117 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 117 171 3 2 39 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 117 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 4 117 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 171 3 1 39 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 117 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 117 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 117 171))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  56 116 171 (Eq.refl Bool.true) (allA_succ_of_accept 55 116 171 (accept_3_4 55 116 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 116 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 116 171 (Polychromatic418967fa.accept_6_5_2_3_1_81 53
  116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 171 (accept_3_4 52
  116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 116 171
  (Polychromatic418967fa.accept_26_25_12_15_1_9693 51 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 116 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 50 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 116 171 (accept_3_4 49 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 116 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 116 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 116 171 (accept_3_4 46 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 116 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 45 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 116 171 (Polychromatic418967fa.accept_13_5_12_2_1_1423 44 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 116 171 (accept_3_4 43 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 116 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 116
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 116 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 116 171 (accept_3_4 40 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 116 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 116 171 (Polychromatic418967fa.accept_16_6_4_11_1_1719 38 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 116 171 (accept_3_4 37 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 116 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 116 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 116 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 116 171 (accept_3_4 34 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 116 171 (Polychromatic418967fa.accept_15_3_11_6_1_3083 33 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 116 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 32 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 116 171 (accept_3_4 31 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 116 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 116 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 116 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 116 171 (accept_3_4 28 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 116 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 116 171 (Polychromatic418967fa.accept_20_6_16_11_1_2379 26 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 116 171 (accept_3_4 25 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 116 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 24 116
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 116 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 116 171 (accept_3_4 22 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 116 171 (Polychromatic418967fa.accept_14_7_4_3_1_488 21 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 116 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 116 171 (accept_3_4 19 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 116 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 116 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 116 171 (accept_3_4 16 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 116 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 116 171 (Polychromatic418967fa.accept_13_1_12_2_1_384 14 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 116 171 (accept_3_4 13 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 116 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 116
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 116 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 116 171 (accept_3_4 10 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  116 171 (Polychromatic418967fa.accept_15_9_11_6_1_637 9 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 116 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 116 171 (accept_3_4 7 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 116 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 116 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 116 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 116 171 (accept_3_4 4 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  116 171 (Polychromatic418967fa.accept_13_3_12_2_1_385 3 116 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 116 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 2 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 116 171 (accept_3_4 1 116 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 116 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 115 171
  (Eq.refl Bool.true) (allA_succ_of_accept 56 115 171 (accept_3_5 56 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 115 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 55 115 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 54 115
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 171 (accept_3_5 53 115
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 171
  (Polychromatic418967fa.accept_6_4_1_3_1_77 52 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 115 171 (Polychromatic418967fa.accept_21_9_10_3_1_262 51 115 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 171 (accept_3_5 50 115 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 115 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 171
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 48 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 171 (accept_3_5 47 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 45 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 171 (accept_3_5 44 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 43 115
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 171
  (Polychromatic418967fa.accept_13_3_11_2_1_1422 42 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 171 (accept_3_5 41 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 39 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 171 (accept_3_5 38 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 171 (Polychromatic418967fa.accept_21_16_10_3_1_9671 37 115
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 171
  (Polychromatic418967fa.accept_10_6_5_1_1_482 36 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 171 (accept_3_5 35 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 171 (accept_3_5 32 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 171 (Polychromatic418967fa.accept_15_1_10_6_1_631 31 115
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 171
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 171 (accept_3_5 29 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 171 (Polychromatic418967fa.accept_15_12_10_6_1_2134 27 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 171 (accept_3_5 26 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 171 (Polychromatic418967fa.accept_20_5_15_11_1_3758 25 115
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 171
  (Polychromatic418967fa.accept_10_4_5_1_1_497 24 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 171 (accept_3_5 23 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 171 (accept_3_5 20 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 115
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 171
  (Polychromatic418967fa.accept_15_3_10_6_1_632 18 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 171 (accept_3_5 17 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 171 (Polychromatic418967fa.accept_16_15_3_11_1_5997 15 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 171 (accept_3_5 14 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 171 (Polychromatic418967fa.accept_20_13_15_11_1_6610 13
  115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 171
  (Polychromatic418967fa.accept_11_1_5_6_1_397 12 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 171 (accept_3_5 11 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 115 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 171 (accept_3_5 8 115 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 171 (Polychromatic418967fa.accept_16_7_3_11_1_3682 7 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 171
  (Polychromatic418967fa.accept_10_6_5_1_1_482 6 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 171 (accept_3_5 5 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 171 (Polychromatic418967fa.accept_13_3_11_2_1_1422 3 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 171 (accept_3_5 2 115 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 1 115 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 114 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 114 171 57 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 56 114 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 114 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 114 171 3 18 38 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 114 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 114 171 3 17 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 114 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 50
  114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 171 3 16 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 114 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412
  46 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 114 171 3 15 38 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 114 171
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 114 171 3 14 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 114 171 3 13 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 114 171 19 2 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 114 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 171 3 12 38 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 171
  (Polychromatic418967fa.accept_10_5_4_1_1_842 35 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 114 171 3 11 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 114 171 (Polychromatic418967fa.accept_12_8_6_3_1_366
  32 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 171
  (Polychromatic418967fa.accept_13_5_10_2_1_856 31 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 171 3 10 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 171 (Polychromatic418967fa.accept_12_4_6_3_1_332
  28 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 114 171 3 9 38 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 114 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 171 3 8 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 171 (Polychromatic418967fa.accept_16_7_2_11_1_931
  23 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 22 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 114 171 3 7 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 114 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 20 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 19 114 171 19 1 6 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 18 114 171 3 6 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 114 171 3 5 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 114 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 171 3 4 38 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 171
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 114 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 114 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 114 171 3 3 38 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 114 171
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 7 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 171 3 2 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 171
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 114 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 114 171 3 1 38 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 114 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 2 114 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 113 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 113 171 (accept_3_4 58 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 171 (accept_3_4 55 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 171 (accept_3_4 52 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 171 (accept_3_4 49 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 171 (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 113 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 171 (accept_3_4 46 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 171 (accept_3_4 43 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 171
  (Polychromatic418967fa.accept_11_8_3_6_1_1855 41 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 171 (accept_3_4 40 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 171 (accept_3_4 37 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 171 (Polychromatic418967fa.accept_21_15_8_3_1_8086 36 113 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 171
  (Polychromatic418967fa.accept_20_15_13_11_1_5110 35 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 113 171 (accept_3_4 34 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 113 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 113 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 171 (accept_3_4 31 113 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 30
  113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 171
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 171 (accept_3_4 28 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 171 (Polychromatic418967fa.accept_13_1_9_2_1_1448 27 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 171 (accept_3_4 25 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 171 (Polychromatic418967fa.accept_13_11_9_2_1_2969 24 113 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 171 (accept_3_4 22 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 171 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 171 (accept_3_4 19 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 171
  (Polychromatic418967fa.accept_15_2_8_6_1_1340 17 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 171 (accept_3_4 16 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 171 (Polychromatic418967fa.accept_16_15_1_11_1_3747 15 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 171 (accept_3_4 13 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 113 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 171 (accept_3_4 10 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 171 (accept_3_4 7 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 171 (accept_3_4 4 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 171 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 113 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 171 (accept_3_4 1 113 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 112
  171 (Eq.refl Bool.true) (allA_succ_of_accept 59 112 171 (accept_3_5 59 112 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 112 171 (Polychromatic418967fa.accept_13_6_8_2_1_1484 58 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 171
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 57 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 171 (accept_3_5 56 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 171 (accept_3_5 53 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 171 (Polychromatic418967fa.accept_21_10_7_3_1_4884 52 112
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 171
  (Polychromatic418967fa.accept_18_15_4_9_1_4204 51 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 171 (accept_3_5 50 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 48 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 171 (accept_3_5 47 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 46 112
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 171
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 45 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 171 (accept_3_5 44 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 171 (accept_3_5 41 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 171 (Polychromatic418967fa.accept_27_13_4_9_1_9692 40 112
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 171
  (Polychromatic418967fa.accept_10_9_2_1_1_840 39 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 171 (accept_3_5 38 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 36 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 171 (accept_3_5 35 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 171 (Polychromatic418967fa.accept_23_11_20_10_1_9664 34
  112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 171
  (Polychromatic418967fa.accept_10_3_2_1_1_839 33 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 171 (accept_3_5 32 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 171 (accept_3_5 29 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 171 (Polychromatic418967fa.accept_15_13_7_6_1_682 28 112
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 171
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 27 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 171 (accept_3_5 26 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 171 (Polychromatic418967fa.accept_17_7_10_1_1_4488 24 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 171 (accept_3_5 23 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 171 (Polychromatic418967fa.accept_21_1_7_3_1_6450 22 112
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 171
  (Polychromatic418967fa.accept_20_1_12_11_1_3778 21 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 112 171 (accept_3_5 20 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 171 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 112
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 171 (accept_3_5 17 112
  171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 16 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 112 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 15 112 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 171 (accept_3_5 14 112 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 171
  (Polychromatic418967fa.accept_15_12_7_6_1_4013 12 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 112 171 (accept_3_5 11 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 112 171 (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 112 171 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 112 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 171 (accept_3_5 8 112 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 6 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 112 171 (accept_3_5 5 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  112 171 (Polychromatic418967fa.accept_11_4_2_6_1_389 4 112 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 112 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 3 112 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 171 (accept_3_5 2 112 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 112 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 111 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 111 171 3 20 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 111 171 (Polychromatic418967fa.accept_17_8_9_1_1_3340 59 111 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 58 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 171 3 19 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 171 (Polychromatic418967fa.accept_18_2_3_9_1_1996 56 111 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 171
  (Polychromatic418967fa.accept_16_7_15_11_1_951 55 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 171 3 18 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 111 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 171 (Polychromatic418967fa.accept_8_4_7_3_1_144
  52 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 171 3 17 37 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 171
  (Polychromatic418967fa.accept_18_14_3_9_1_4234 50 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 49 111 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 171 3 16 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 171 (Polychromatic418967fa.accept_13_8_7_2_1_2988
  47 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 46 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 171 3 15 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 111 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 171 (Polychromatic418967fa.accept_18_7_3_9_1_1020
  43 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 171 3 14 37 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 171
  (Polychromatic418967fa.accept_21_20_6_3_1_9691 41 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 171 (Polychromatic418967fa.accept_11_7_1_6_1_1281 40 111 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 171 3 13 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 171 (Polychromatic418967fa.accept_11_5_1_6_1_774
  38 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 171 3 12 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 171 (Polychromatic418967fa.accept_13_9_7_2_1_3869 35 111 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 171
  (Polychromatic418967fa.accept_13_8_7_2_1_2988 34 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 171 3 11 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 111 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 171 (Polychromatic418967fa.accept_13_5_7_2_1_852
  31 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 171 3 10 37 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 171
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 29 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 111 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 171 3 9 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 171
  (Polychromatic418967fa.accept_16_10_15_11_1_3785 26 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 111 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 111 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 171 3 8 37 57 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 23 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 111 171 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 111 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 171 3 7 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 171 (Polychromatic418967fa.accept_8_4_7_3_1_144 20
  111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 171
  (Polychromatic418967fa.accept_16_3_15_11_1_2676 19 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 111 171 3 6 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 111 171 (Polychromatic418967fa.accept_16_1_15_11_1_356 17 111 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 16 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 171 3 5 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 171 (Polychromatic418967fa.accept_18_14_3_9_1_4234 14 111 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 171 (Polychromatic418967fa.accept_18_13_3_9_1_4233 13 111
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 171 3 4 37 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 171
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 171 (Polychromatic418967fa.accept_14_10_13_3_1_2552 10 111 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 171 3 3 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 171 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8
  111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 171
  (Polychromatic418967fa.accept_11_7_1_6_1_1281 7 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 171 3 2 37 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 171 (Polychromatic418967fa.accept_11_5_1_6_1_774 5 111 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 111 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 171 3 1 37 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 171
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 111 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 171 (Polychromatic418967fa.accept_16_1_15_11_1_356 1 111 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 62 110 171 (Eq.refl Bool.true) (allA_succ_of_accept 61 110 171 (accept_3_4 61 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 110 171 (Polychromatic418967fa.accept_13_8_6_2_1_865 60 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 110 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 110 171 (accept_3_4 58 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 110 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 110 171 (Polychromatic418967fa.accept_13_4_6_2_1_1437 56 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 110 171 (accept_3_4 55 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 110 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 110
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 171 (accept_3_4 52 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 110 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 110 171 (accept_3_4 49 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 110 171 (Polychromatic418967fa.accept_13_9_6_2_1_2200 48 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 110 171 (accept_3_4 46 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 110 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 110 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 110 171 (accept_3_4 43 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 110 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 110 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 110 171 (accept_3_4 40 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 110 171 (Polychromatic418967fa.accept_18_3_2_9_1_1013 39 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 110 171 (Polychromatic418967fa.accept_13_12_6_2_1_1441 38 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 171 (accept_3_4 37 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 110 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 110 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 110 171 (accept_3_4 34 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 110 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 110 171 (Polychromatic418967fa.accept_23_9_18_10_1_9690 32 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 110 171 (accept_3_4 31 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 110 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 110 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 110 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 110 171 (accept_3_4 28 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 110 171 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 110 171 (Polychromatic418967fa.accept_15_11_5_6_1_669 26 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 110 171 (accept_3_4 25 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 110 171 (Polychromatic418967fa.accept_17_7_8_1_1_1373 24 110
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 110 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 110 171 (accept_3_4 22 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 110 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 110 171 (Polychromatic418967fa.accept_25_20_10_21_1_9689 20 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 110 171 (accept_3_4 19 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 110
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 171 (accept_3_4 16 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 110 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 110 171 (Polychromatic418967fa.accept_13_1_6_2_1_377 14 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 110 171 (accept_3_4 13 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 110 171 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 110
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 110 171 (accept_3_4 10 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  110 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 110 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 171 (accept_3_4 7 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 110 171 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 110 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 110 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 110 171 (accept_3_4 4 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  110 171 (Polychromatic418967fa.accept_15_3_5_6_1_4005 3 110 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 110 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 110 171 (accept_3_4 1 110 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 110 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  109 171 (Eq.refl Bool.true) (allA_succ_of_accept 62 109 171 (accept_3_5 62 109 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 109 171 (Polychromatic418967fa.accept_13_9_5_2_1_2185 61 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 171
  (Polychromatic418967fa.accept_11_5_10_6_1_793 60 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 171 (accept_3_5 59 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 171 (accept_3_5 56 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 171 (accept_3_5 53 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 171 (Polychromatic418967fa.accept_13_12_5_2_1_2173 51 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 171 (accept_3_5 50 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 171 (Polychromatic418967fa.accept_11_5_10_6_1_793 49 109
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 171 (accept_3_5 47 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 45 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 171 (accept_3_5 44 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 109 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 171 (accept_3_5 41 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 171 (Polychromatic418967fa.accept_15_9_4_6_1_3075 39 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 171 (accept_3_5 38 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 171 (Polychromatic418967fa.accept_25_12_9_21_1_9688 37 109
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 171
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 171 (accept_3_5 35 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 171 (accept_3_5 32 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 171 (Polychromatic418967fa.accept_50_31_9_21_1_9687 31 109
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 171 (accept_3_5 29 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 171 (accept_3_5 26 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 171 (Polychromatic418967fa.accept_10_5_9_1_1_187 25 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 171
  (Polychromatic418967fa.accept_15_9_4_6_1_3075 24 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 171 (accept_3_5 23 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 171 (accept_3_5 20 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 171 (Polychromatic418967fa.accept_22_19_21_17_1_6283 19
  109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 171 (accept_3_5 17 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 171 (accept_3_5 14 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 171 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 171
  (Polychromatic418967fa.accept_10_2_9_1_1_185 12 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 171 (accept_3_5 11 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 171 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 171 (accept_3_5 8 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 171 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 171 (accept_3_5 5 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 171 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 171 (accept_3_5 2 109 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 108 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 108 171 9 7 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 62 108 171 (Polychromatic418967fa.accept_14_6_10_3_1_1038 62 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 171 (Polychromatic418967fa.accept_15_1_3_6_1_621 61 108
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 108 171 3 20 36 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 108 171
  (Polychromatic418967fa.accept_10_9_8_1_1_1331 59 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 108 171 (Polychromatic418967fa.accept_11_3_9_6_1_105 58 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 108 171 3 19 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 108 171 (Polychromatic418967fa.accept_15_11_3_6_1_1306
  56 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 171
  (Polychromatic418967fa.accept_8_7_4_3_1_156 55 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 171 9 6 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 53 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 171 (Polychromatic418967fa.accept_16_4_12_11_1_2650 52 108
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 108 171 3 17 36 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 108 171
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 50 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 108 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 49 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 108 171 3 16 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 108 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 47
  108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 171
  (Polychromatic418967fa.accept_15_1_3_6_1_621 46 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 108 171 9 5 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 108 171 (Polychromatic418967fa.accept_13_5_4_2_1_846 44 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 43 108
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 108 171 3 14 36 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 171
  (Polychromatic418967fa.accept_14_13_10_3_1_1037 41 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 108 171 (Polychromatic418967fa.accept_15_10_3_6_1_3042 40 108 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 108 171 3 13 36 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 108 171
  (Polychromatic418967fa.accept_13_12_4_2_1_2955 38 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 108 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954 37 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 108 171 9 4 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 108 171 (Polychromatic418967fa.accept_14_7_10_3_1_1034
  35 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 171
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 34 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 108 171 3 11 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 108 171 (Polychromatic418967fa.accept_13_6_4_2_1_1433 32 108 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 171
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 171 3 10 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 29 108 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 171
  (Polychromatic418967fa.accept_23_5_16_10_1_9686 28 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 108 171 9 3 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 108 171 (Polychromatic418967fa.accept_15_11_3_6_1_1306 26 108 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 25 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 171 3 8 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 171 (Polychromatic418967fa.accept_17_5_6_1_1_5735 22 108
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 171 3 7 36 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 171
  (Polychromatic418967fa.accept_14_6_10_3_1_1038 20 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 171 (Polychromatic418967fa.accept_10_9_8_1_1_1331 19 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 171 9 2 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 171
  (Polychromatic418967fa.accept_16_1_12_11_1_2648 17 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 108 171 (Polychromatic418967fa.accept_15_1_3_6_1_621 16 108 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 171 3 5 36 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 171
  (Polychromatic418967fa.accept_11_3_9_6_1_105 14 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 171 (Polychromatic418967fa.accept_10_3_8_1_1_182 13 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 171 3 4 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 171 (Polychromatic418967fa.accept_13_11_4_2_1_2954
  11 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 171
  (Polychromatic418967fa.accept_15_10_3_6_1_3042 10 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 108 171 9 1 12 19 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 108 171 (Polychromatic418967fa.accept_16_8_12_11_1_3697 8 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 171 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 171 3 2 36 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 171
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 171 (Polychromatic418967fa.accept_16_4_12_11_1_2650 4 108 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 171 3 1 36 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 171 (Polychromatic418967fa.accept_17_2_6_1_1_8357 2 108 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 171
  (Polychromatic418967fa.accept_15_1_3_6_1_621 1 108 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 107 171 (Eq.refl
  Bool.true) (allA_succ_of_accept 64 107 171 (accept_3_4 64 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 107 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 63 107 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 107 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 171 (accept_3_4 61 107 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 171
  (Polychromatic418967fa.accept_21_18_2_3_1_9685 60 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 107 171 (Polychromatic418967fa.accept_21_17_2_3_1_4942 59 107 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 171 (accept_3_4 58 107 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 107 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 171 (Polychromatic418967fa.accept_6_2_5_3_1_16 56
  107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 171 (accept_3_4 55
  107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 171
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 107 171 (Polychromatic418967fa.accept_13_1_3_2_1_1429 53 107 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 171 (accept_3_4 52 107 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 107 171 (Polychromatic418967fa.accept_13_12_3_2_1_1470 51 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 171 (accept_3_4 49 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 171 (accept_3_4 46 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 171 (accept_3_4 43 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 171 (Polychromatic418967fa.accept_15_12_2_6_1_2127 42 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 171 (accept_3_4 40 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 171 (Polychromatic418967fa.accept_21_18_2_3_1_9685 39 107 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 171 (accept_3_4 37 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 171 (Polychromatic418967fa.accept_13_9_3_2_1_399 35 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 171 (accept_3_4 34 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 107 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 171 (accept_3_4 31 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 171 (Polychromatic418967fa.accept_18_12_17_9_1_5513 30 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 171 (accept_3_4 28 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 171 (accept_3_4 25 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 171 (Polychromatic418967fa.accept_10_4_7_1_1_471 24 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 171 (Polychromatic418967fa.accept_13_10_3_2_1_4728 23 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 171 (accept_3_4 22 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 107
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 171 (accept_3_4 19 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 171 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 171 (Polychromatic418967fa.accept_21_17_2_3_1_4942 17 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 171 (accept_3_4 16 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 171 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 107 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 171 (accept_3_4 13 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 171 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 171 (accept_3_4 10 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 171 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 171 (accept_3_4 7 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 171 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 171 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 171 (accept_3_4 4 107 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 171 (Polychromatic418967fa.accept_11_3_8_6_1_788 3 107 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 171
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 171 (accept_3_4 1 107 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 106 171 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 106 171 (accept_3_5 65 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 171 (Polychromatic418967fa.accept_22_20_18_17_1_9616 64 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 106 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 63 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 171 (accept_3_5 62 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 171 (accept_3_5 59 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 171 (accept_3_5 56 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 171 (accept_3_5 53 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 52 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 171 (accept_3_5 50 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 171
  (Polychromatic418967fa.accept_15_3_1_6_1_206 48 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 171 (accept_3_5 47 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 171 (accept_3_5 44 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 171
  (Polychromatic418967fa.accept_10_2_6_1_1_1296 42 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 171 (accept_3_5 41 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 171 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 171 (accept_3_5 38 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 171
  (Polychromatic418967fa.accept_20_16_6_11_1_9657 36 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 106 171 (accept_3_5 35 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 106 171 (Polychromatic418967fa.accept_11_1_7_6_1_378 34 106 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 171 (accept_3_5 32 106 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 171
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 171 (accept_3_5 29 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 171 (Polychromatic418967fa.accept_16_12_10_11_1_2667 28 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 106 171 (Polychromatic418967fa.accept_10_7_6_1_1_486 27 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 171 (accept_3_5 26 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 171
  (Polychromatic418967fa.accept_15_9_1_6_1_657 24 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 171 (accept_3_5 23 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 171 (Polychromatic418967fa.accept_10_2_6_1_1_1296 22 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 171 (accept_3_5 20 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 171
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 171 (accept_3_5 17 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 171 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 171 (Polychromatic418967fa.accept_10_5_6_1_1_836 15 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 171 (accept_3_5 14 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 171
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 171 (accept_3_5 11 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 171 (Polychromatic418967fa.accept_15_10_1_6_1_3033 10 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 171 (accept_3_5 8 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 171 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 171
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 171 (accept_3_5 5 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 171 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 106 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 171 (Polychromatic418967fa.accept_15_3_1_6_1_206 3 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 171 (accept_3_5 2 106 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 105 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 105 171 3 22 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 65 105 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 171 (Polychromatic418967fa.accept_10_4_5_1_1_497
  64 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 171 3 21 35 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 171 3 20 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325
  59 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 105 171 3 19 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 105 171 (Polychromatic418967fa.accept_10_6_5_1_1_482 56 105 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 171 (Polychromatic418967fa.accept_12_7_9_3_1_767
  55 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 105 171 3 18 35 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 171 (Polychromatic418967fa.accept_14_10_7_3_1_1022 52 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 171 3 17 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 171
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 49 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 105 171 3 16 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 105 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 47 105 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 171 3 15 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 105 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 44 105 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 171 (Polychromatic418967fa.accept_12_7_9_3_1_767
  43 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 171 3 14 35 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 171
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 105 171 (Polychromatic418967fa.accept_17_6_3_1_1_7011 40 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 105 171 3 13 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 37 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 105 171 3 12 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 105 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 105 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 171 3 11 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 171 (Polychromatic418967fa.accept_13_6_1_2_1_1464 32 105 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 171 3 10 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 105 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 29 105 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 171
  (Polychromatic418967fa.accept_18_10_15_9_1_1054 28 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 105 171 3 9 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 105 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 171
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 105 171 3 8 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 105 171 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 171 3 7 35 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 171
  (Polychromatic418967fa.accept_16_4_9_11_1_7159 20 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 171 (Polychromatic418967fa.accept_10_9_5_1_1_1325 19 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 171 3 6 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 171
  (Polychromatic418967fa.accept_10_6_5_1_1_482 16 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 171 3 5 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 105
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 171 3 4 35 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 171
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 171 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 171 3 3 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 171 (Polychromatic418967fa.accept_24_8_9_3_1_9684 8 105 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 171
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 105 171 3 2 35 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 171 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 171 (Polychromatic418967fa.accept_10_4_5_1_1_497 4 105 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 171 3 1 35 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 171
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 171 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 105 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 68 104 171 (Eq.refl Bool.true) (allA_succ_of_accept 67 104 171 (accept_3_4 67 104 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 104 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 65 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 104 171 (accept_3_4 64 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 104 171 (Polychromatic418967fa.accept_22_19_16_17_1_9683 63 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 171 (Polychromatic418967fa.accept_22_18_16_17_1_8011 62 104 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 171 (accept_3_4 61 104 171
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 171 (Polychromatic418967fa.accept_7_4_6_3_1_271
  60 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 59 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 104 171 (accept_3_4 58 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 104 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 57 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 104 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 56 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 171 (accept_3_4 55 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 54 104
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 104 171 (accept_3_4 52 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 104 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 104 171 (Polychromatic418967fa.accept_15_5_14_6_1_5120 50 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 104 171 (accept_3_4 49 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 104 171 (Polychromatic418967fa.accept_21_6_20_3_1_9617 48 104
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 104 171 (accept_3_4 46 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 104 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 45 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 104 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 104 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 171 (accept_3_4 43 104 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 104 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 104 171 (accept_3_4 40 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 104 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 104 171 (Polychromatic418967fa.accept_14_10_6_3_1_1055 38 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 171 (accept_3_4 37 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 171 (Polychromatic418967fa.accept_16_4_8_11_1_5961 36 104
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 171 (accept_3_4 34 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 171 (Polychromatic418967fa.accept_17_16_2_1_1_4492 33 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 32 104 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 171 (accept_3_4 31 104 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 171 (accept_3_4 28 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 171 (Polychromatic418967fa.accept_10_7_4_1_1_1319 27 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 171 (Polychromatic418967fa.accept_24_2_8_3_1_7844 26 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 171 (accept_3_4 25 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 171 (Polychromatic418967fa.accept_14_10_6_3_1_1055 24 104
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 171 (accept_3_4 22 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 171 (Polychromatic418967fa.accept_11_10_5_6_1_1842 21 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 171 (Polychromatic418967fa.accept_15_5_14_6_1_5120 20 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 171 (accept_3_4 19 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 171 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 104 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 171 (accept_3_4 16 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 171 (Polychromatic418967fa.accept_10_5_4_1_1_842 15 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 171 (Polychromatic418967fa.accept_23_14_12_10_1_9682 14 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 171 (accept_3_4 13 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 171 (Polychromatic418967fa.accept_11_1_5_6_1_397 12 104
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 171 (accept_3_4 10 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 171 (Polychromatic418967fa.accept_15_8_14_6_1_3003 8 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 171 (accept_3_4 7 104 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 171 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 104 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 171
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 171 (accept_3_4 4 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 171 (Polychromatic418967fa.accept_16_3_8_11_1_2714 3 104 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 171 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 104 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 171 (accept_3_4 1 104 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 171)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  69 103 171 (Eq.refl Bool.true) (allA_succ_of_accept 68 103 171 (accept_3_5 68 103 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 103 171 (Polychromatic418967fa.accept_15_7_13_6_1_696 67 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 171
  (Polychromatic418967fa.accept_13_1_12_2_1_384 66 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 171 (accept_3_5 65 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 171 (Polychromatic418967fa.accept_16_15_7_11_1_3760 63 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 171 (accept_3_5 62 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 171 (Polychromatic418967fa.accept_28_5_19_3_1_9681 61 103
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 171
  (Polychromatic418967fa.accept_8_4_7_3_1_144 60 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 171 (accept_3_5 59 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 171 (accept_3_5 56 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 171 (Polychromatic418967fa.accept_13_3_12_2_1_385 55 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 171
  (Polychromatic418967fa.accept_14_12_5_3_1_1011 54 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 171 (accept_3_5 53 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 171 (accept_3_5 50 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 171 (Polychromatic418967fa.accept_13_10_12_2_1_1460 49 103 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 171
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 48 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 171 (accept_3_5 47 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 171 (accept_3_5 44 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 171
  (Polychromatic418967fa.accept_10_2_3_1_1_481 42 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 171 (accept_3_5 41 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 171 (Polychromatic418967fa.accept_18_3_13_9_1_4260 39 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 171 (accept_3_5 38 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 103 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 171
  (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 171 (accept_3_5 35 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 171 (accept_3_5 32 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 171 (Polychromatic418967fa.accept_13_5_12_2_1_1423 31 103
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 171
  (Polychromatic418967fa.accept_7_2_5_3_1_98 30 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 171 (accept_3_5 29 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 171 (Polychromatic418967fa.accept_13_1_12_2_1_384 27 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 171 (accept_3_5 26 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 171 (Polychromatic418967fa.accept_27_25_22_9_1_9680 25 103
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 171
  (Polychromatic418967fa.accept_11_2_4_6_1_2412 24 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 171 (accept_3_5 23 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 171 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 171 (accept_3_5 20 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 171 (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 103
  171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 171
  (Polychromatic418967fa.accept_10_8_3_1_1_1316 18 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 171 (accept_3_5 17 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 171 (accept_3_5 14 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 171 (Polychromatic418967fa.accept_11_2_4_6_1_2412 13 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 171
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 171 (accept_3_5 11 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 171 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 171 (accept_3_5 8 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 171 (Polychromatic418967fa.accept_15_7_13_6_1_696 7 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 171
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 171 (accept_3_5 5 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 171 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 171 (Polychromatic418967fa.accept_13_3_12_2_1_385 3 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 171 (accept_3_5 2 103 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 171 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 102 171 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 102 171 3 23 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 102 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 102 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 171
  (Polychromatic418967fa.accept_15_7_12_6_1_1327 67 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 171 3 22 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 64
  102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 102 171 3 21 34 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 102 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 102 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 171 3 20 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 171 (Polychromatic418967fa.accept_10_9_2_1_1_840
  59 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 171
  (Polychromatic418967fa.accept_12_10_6_3_1_786 58 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 102 171 3 19 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 102 171 (Polychromatic418967fa.accept_10_6_2_1_1_494 56 102 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 171 (Polychromatic418967fa.accept_7_6_4_3_1_266
  55 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 102 171 3 18 34 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 102 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 171 (Polychromatic418967fa.accept_11_8_3_6_1_1855 52 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 102 171 3 17 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 102 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 50
  102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 171 3 16 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 171 (Polychromatic418967fa.accept_15_2_12_6_1_3063 47 102 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 46 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 102 171 3 15 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 102 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 102 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 43
  102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 171 3 14 34 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 102 171 3 13 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 102 171 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 171 3 12 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 171 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 102 171 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 34 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 102 171 3 11 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 102 171 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 102 171 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 171 (Polychromatic418967fa.accept_11_9_3_6_1_797
  31 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 102 171 3 10 34 57
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 102 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 102 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 28 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 102 171 3 9 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 102 171 (Polychromatic418967fa.accept_10_6_2_1_1_494
  26 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 171
  (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 102 171 3 8 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 102 171 (Polychromatic418967fa.accept_10_3_2_1_1_839 23 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 102 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 102 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 102 171 3 7 34 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 102 171
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 171 (Polychromatic418967fa.accept_10_9_2_1_1_840 19 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 102 171 3 6 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 102 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 171
  (Polychromatic418967fa.accept_10_6_2_1_1_494 16 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 102 171 3 5 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 102 171 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 171 3 4 34 57 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 171
  (Polychromatic418967fa.accept_18_11_12_9_1_992 11 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 171 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 102 171 3 3 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 102 171 (Polychromatic418967fa.accept_7_1_4_3_1_21 8 102 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 171
  (Polychromatic418967fa.accept_14_7_4_3_1_488 7 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 171 3 2 34 57 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 171 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 102 171
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 171 3 1 34 57 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 171
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 102 171 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 171 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 171 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102
  171))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_171_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


