-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch188
-- name    : Polychromatic418967fa_Branch188
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:19:53.483973+00:00
-- url     : https://prove2.me/theorems/f2fdf2ed-923c-4f83-a845-4a3bb8973b37
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch188_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_188 : allB 188 188 :=
  allB_succ' 2 187 188 (Eq.refl Bool.true) (allA_of_3_0 2 187 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  186 188 (Eq.refl Bool.true) (allA_succ_of_gcd 2 186 188 2 1 93 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 188 (accept_3_2 1 186 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 186 188))) (allB_succ' 4 185 188 (Eq.refl Bool.true) (allA_succ_of_accept 3 185 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 185 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 185 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 185 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 188 (accept_3_2 1 185 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 185 188)))) (allB_succ' 5 184 188 (Eq.refl Bool.true) (allA_of_3_0 5 184 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 183 188 (Eq.refl Bool.true) (allA_succ_of_accept 5 183 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 183 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 188 (accept_3_2 4 183 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 183 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 183 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 188 (accept_3_2 1 183 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 188)))))) (allB_succ' 7 182 188 (Eq.refl Bool.true) (allA_succ_of_gcd 6 182 188 2 3
  91 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 182 188
  (Polychromatic418967fa.accept_9_5_2_8_1_109 5 182 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 182 188 2 2 91 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 182 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 3 182 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 188 2 1 91 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 188 (accept_3_2 1 182 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 182 188))))))) (allB_succ' 8 181 188 (Eq.refl Bool.true) (allA_of_3_0 8 181 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 180 188 (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 188 4 2 45 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 188
  (accept_3_2 7 180 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 188 2 3 90 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 188
  (Polychromatic418967fa.accept_13_5_11_6_1_505 5 180 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 180 188 4 1 45 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 180 188 (Polychromatic418967fa.accept_16_3_4_12_1_3799 3 180 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 188 2 1 90 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 188 (accept_3_2 1 180 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 180 188))))))))) (allB_succ' 10 179 188 (Eq.refl Bool.true) (allA_succ_of_accept 9 179 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 9 179 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 179 188 (Polychromatic418967fa.accept_16_8_3_12_1_1819 8 179 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 188 (accept_3_2 7 179 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 179 188 (Polychromatic418967fa.accept_15_6_14_8_1_245 6 179 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5
  179 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 188 (accept_3_2 4 179
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 188 (Polychromatic418967fa.accept_6_3_5_2_1_12
  3 179 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 188
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 179 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 188 (accept_3_2 1 179 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  188)))))))))) (allB_succ' 11 178 188 (Eq.refl Bool.true) (allA_of_3_0 11 178 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 12 177 188 (Eq.refl Bool.true) (allA_succ_of_accept 11 177 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 177 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 188 (accept_3_2 10 177 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 188 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 177 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 177 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 188 (accept_3_2 7 177 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 177 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 188 (accept_3_2 4 177 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 177 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 177 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 188 (accept_3_2 1 177 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 177 188)))))))))))) (allB_succ' 13 176 188 (Eq.refl Bool.true) (allA_succ_of_gcd 12 176
  188 4 3 44 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11
  176 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 11 176 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 176 188 2 5 88 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 176 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 176 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 188 4 2 44 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 188 (accept_3_2 7 176 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 188 2 3 88 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 176 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 188 4 1 44 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 3 176 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 176 188 2 1 88 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 176 188 (accept_3_2 1 176 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  188))))))))))))) (allB_succ' 14 175 188 (Eq.refl Bool.true) (allA_of_3_0 14 175 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 174 188 (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 188 2 7 87 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 188 (accept_3_2 13 174 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 188 2 6 87 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 188
  (Polychromatic418967fa.accept_9_2_3_8_1_318 11 174 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 188 2 5 87 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 174 188 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 174 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 174 188 2 4 87 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 188 (accept_3_2 7 174 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 174 188 2 3 87 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 174 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 174 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 188 2 2 87 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 174 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  174 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 188 2 1 87 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 188 (accept_3_2 1
  174 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 188))))))))))))))) (allB_succ' 16 173 188 (Eq.refl
  Bool.true) (allA_succ_of_accept 15 173 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 173 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 188 (Polychromatic418967fa.accept_9_5_2_8_1_109
  14 173 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 188 (accept_3_2 13
  173 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 12 173 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 173 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 173 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 188 (accept_3_2 10 173 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 173 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 8
  173 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 188 (accept_3_2 7 173
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 6 173 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 173 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 173 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 188 (accept_3_2 4 173 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 173 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 173 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 188 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  173 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 188 (accept_3_2 1 173
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173 188)))))))))))))))) (allB_succ' 17 172 188 (Eq.refl
  Bool.true) (allA_of_3_0 17 172 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 171 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 171 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 171 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 188 (accept_3_2 16 171 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 171 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 171 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 188 (Polychromatic418967fa.accept_13_1_2_6_1_515
  14 171 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 188 (accept_3_2 13
  171 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 188
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 171 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 171 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 171 188 (accept_3_2 10 171 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 171 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 171 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 171 188 (Polychromatic418967fa.accept_13_8_2_6_1_2385
  8 171 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 188 (accept_3_2 7
  171 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 188
  (Polychromatic418967fa.accept_12_6_3_8_1_512 6 171 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 171 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 171 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 188 (accept_3_2 4 171 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 171 188 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 171 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 171 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 2
  171 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 188 (accept_3_2 1 171
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171 188)))))))))))))))))) (allB_succ' 19 170 188 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 170 188 2 9 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 170 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 188 2 8 85 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 170 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 188 2 7 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 170 188 (accept_3_2 13 170 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  170 188 2 6 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 170 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 170 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 170 188 2 5 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 170 188 (Polychromatic418967fa.accept_13_9_1_6_1_510 9 170 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 188 2 4 85 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 188 (accept_3_2 7 170 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170 188 2 3 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 170 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 170 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 170 188 2 2 85 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 170 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 170 188 2 1 85 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 170 188 (accept_3_2 1 170 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  188))))))))))))))))))) (allB_succ' 20 169 188 (Eq.refl Bool.true) (allA_of_3_0 20 169 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 168 188 (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 188 4 5 42 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 188 (accept_3_2 19 168 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 188 2 9 84 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 188
  (Polychromatic418967fa.accept_16_1_8_12_1_405 17 168 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 188 4 4 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 168 188 (Polychromatic418967fa.accept_13_2_12_6_1_2394 15 168 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 188 2 7 84 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 188 (accept_3_2 13 168 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 188 4 3 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 11 168 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 188 2 5 84 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 188
  (Polychromatic418967fa.accept_15_9_3_8_1_3155 9 168 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 188 4 2 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 188 (accept_3_2 7 168 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168
  188 2 3 84 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 168 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 188 4 1 42 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 168 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 168 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 188 2 1 84 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 188 (accept_3_2 1 168 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 168 188))))))))))))))))))))) (allB_succ' 22 167 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 167 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 167 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 20 167 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 188 (accept_3_2 19 167 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 188 (Polychromatic418967fa.accept_13_5_11_6_1_505
  18 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 167 188
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 167 188 (accept_3_2 16 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 188 (Polychromatic418967fa.accept_11_3_2_1_1_994 14 167 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 188 (accept_3_2 13 167 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 167 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 188
  (Polychromatic418967fa.accept_8_3_7_4_1_42 11 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 188 (accept_3_2 10 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 188 (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 167 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 188 (accept_3_2 7 167 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 167 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 188
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 188 (accept_3_2 4 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 2 167 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 188 (accept_3_2 1 167 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 188)))))))))))))))))))))) (allB_succ' 23 166 188 (Eq.refl Bool.true) (allA_of_3_0
  23 166 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 165 188 (Eq.refl Bool.true) (allA_succ_of_accept 23
  165 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 165 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 165 188 (accept_3_2 22 165 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 165 188 (Polychromatic418967fa.accept_22_21_11_12_1_10810 21 165 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 188 (Polychromatic418967fa.accept_9_2_3_8_1_318
  20 165 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 188 (accept_3_2 19
  165 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 188
  (Polychromatic418967fa.accept_12_6_9_8_1_165 18 165 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 165 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 188 (accept_3_2 16 165 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 165 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 15 165 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 165 188 (Polychromatic418967fa.accept_9_5_3_8_1_316
  14 165 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 188 (accept_3_2 13
  165 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 188
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 165 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 165 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 165 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 188 (accept_3_2 10 165 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 165 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 165 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 165 188 (Polychromatic418967fa.accept_16_8_5_12_1_3812
  8 165 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 188 (accept_3_2 7
  165 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 188
  (Polychromatic418967fa.accept_9_6_3_8_1_595 6 165 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 165 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 188 (accept_3_2 4 165 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 165 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 165 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 165 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 2
  165 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 188 (accept_3_2 1 165
  188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 188)))))))))))))))))))))))) (allB_succ' 25 164 188 (Eq.refl
  Bool.true) (allA_succ_of_gcd 24 164 188 4 6 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 164 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 188 2 11 82 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 164 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 188 4 5 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 164 188 (accept_3_2 19 164 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  164 188 2 9 82 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 164 188 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 164 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 164 188 4 4 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 164 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 15 164 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 188 2 7 82 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 188 (accept_3_2 13 164 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 188 4 3 41 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 164 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 164 188 2 5 82 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 164 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 164 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 164 188 4 2 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 164 188 (accept_3_2 7 164 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 164 188 2 3 82 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 164 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 164 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 164 188 4 1 41 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 164 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  164 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 188 2 1 82 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 188 (accept_3_2 1
  164 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164 188))))))))))))))))))))))))) (allB_succ' 26 163 188
  (Eq.refl Bool.true) (allA_of_3_0 26 163 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 162 188 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 162 188 2 13 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 162 188 (accept_3_2 25 162 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 188 2 12 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 162 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 188 2 11 81 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 162 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 188 2 10 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 188 (accept_3_2 19 162 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 188 2 9 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 188 (Polychromatic418967fa.accept_16_1_2_12_1_1757 17 162 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 188 2 8 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 188 (Polychromatic418967fa.accept_10_5_2_8_1_135
  15 162 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 162 188 2 7 81 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 188
  (accept_3_2 13 162 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 188 2 6 81 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 188
  (Polychromatic418967fa.accept_15_11_12_8_1_739 11 162 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 188 2 5 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 162 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 162 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 162 188 2 4 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 188 (accept_3_2 7 162 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 162 188 2 3 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 162 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 162 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 188 2 2 81 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 162 188 (Polychromatic418967fa.accept_12_3_6_8_1_969 3
  162 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 188 2 1 81 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 188 (accept_3_2 1
  162 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 188))))))))))))))))))))))))))) (allB_succ' 28 161 188
  (Eq.refl Bool.true) (allA_succ_of_accept 27 161 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 161 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 188 (accept_3_2 25 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 188 (Polychromatic418967fa.accept_13_11_5_6_1_519 24 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 188 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 161 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 188 (accept_3_2 22 161 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 188
  (Polychromatic418967fa.accept_15_5_11_8_1_1391 20 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 188 (accept_3_2 19 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 188 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 188 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 161 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 188 (accept_3_2 16 161 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 161 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 188 (accept_3_2 13 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 188 (Polychromatic418967fa.accept_13_12_5_6_1_1050 12 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 188 (Polychromatic418967fa.accept_13_11_5_6_1_519 11 161 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 188 (accept_3_2 10 161 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 188
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 188 (accept_3_2 7 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 188 (Polychromatic418967fa.accept_11_6_7_1_1_564 6 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 5 161 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 188 (accept_3_2 4 161 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 161 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 188 (accept_3_2 1 161 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  188)))))))))))))))))))))))))))) (allB_succ' 29 160 188 (Eq.refl Bool.true) (allA_of_3_0 29 160 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 159 188 (Eq.refl Bool.true) (allA_succ_of_accept 29 159 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 188 (accept_3_2 28 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 27 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 188 (Polychromatic418967fa.accept_22_4_5_12_1_10809 26 159 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 188 (accept_3_2 25 159 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 188 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 159
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 188 (accept_3_2 22 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 159 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 188 (accept_3_2 19 159 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 159 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 188 (accept_3_2 16 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 159 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 188 (accept_3_2 13 159 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 12 159 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 188 (accept_3_2 10 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 188 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 159 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 188 (accept_3_2 7 159 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 188 (Polychromatic418967fa.accept_11_6_5_1_1_586 6 159 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 188 (accept_3_2 4 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 3 159 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 2 159 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 188 (accept_3_2 1 159 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159 188)))))))))))))))))))))))))))))) (allB_succ' 31 158 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 158 188 2 15 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 29 158 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 188 2 14 79 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 188
  (Polychromatic418967fa.accept_13_1_2_6_1_515 27 158 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 188 2 13 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 188 (accept_3_2 25 158 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 188 2 12 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 158 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 188 2 11 79 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 158 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 188 2 10 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 188 (accept_3_2 19 158 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 188 2 9 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 158 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 158 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 188 2 8 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 15
  158 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 158 188 2 7 79 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 158 188 (accept_3_2 13
  158 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 158 188 2 6 79 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 158 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 158 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 158 188 2 5 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 158 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 158 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 188 2 4 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 188 (accept_3_2 7 158 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 158 188 2 3 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 158 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 158 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 188 2 2 79 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  158 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 188 2 1 79 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 188 (accept_3_2 1
  158 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 188))))))))))))))))))))))))))))))) (allB_succ' 32 157
  188 (Eq.refl Bool.true) (allA_of_3_0 32 157 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 156 188
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 188 4 8 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 156 188 (accept_3_2 31 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 188 2 15 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 156 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 188 4 7 39 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 188
  (Polychromatic418967fa.accept_19_8_4_17_1_9510 27 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 188 2 13 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 188 (accept_3_2 25 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 188 4 6 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 156 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 23 156 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 188 2 11 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 188 (Polychromatic418967fa.accept_11_10_2_1_1_1036
  21 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 156 188 4 5 39 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 188
  (accept_3_2 19 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 188 2 9 78 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 156 188 4 4 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 156 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 156 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 188 2 7 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 188 (accept_3_2 13 156 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 188 4 3 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 156 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 188 2 5 78 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 188
  (Polychromatic418967fa.accept_17_9_3_1_1_2275 9 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 188 4 2 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 188 (accept_3_2 7 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156
  188 2 3 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 5 156 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 188 4 1 39 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 156 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 188 2 1 78 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 188 (accept_3_2 1 156 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 156 188))))))))))))))))))))))))))))))))) (allB_succ' 34 155 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 33 155 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 155 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 32 155 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 188 (accept_3_2 31 155 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 188 (Polychromatic418967fa.accept_7_2_1_6_1_173
  30 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 188
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 188 (accept_3_2 28 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 155 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 188 (accept_3_2 25 155 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 24 155 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 188
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 188 (accept_3_2 22 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 188 (Polychromatic418967fa.accept_13_7_12_6_1_1039 20 155 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 188 (accept_3_2 19 155 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 188 (Polychromatic418967fa.accept_13_5_12_6_1_508 18 155
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 188
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 188 (accept_3_2 16 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 14 155 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 188 (accept_3_2 13 155 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 155 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 188
  (Polychromatic418967fa.accept_15_11_5_8_1_3157 11 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 188 (accept_3_2 10 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 188 (Polychromatic418967fa.accept_16_8_11_12_1_962 8 155 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 188 (accept_3_2 7 155 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 6 155 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 188
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 188 (accept_3_2 4 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 155 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 188 (accept_3_2 1 155 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 188)))))))))))))))))))))))))))))))))) (allB_succ' 35 154 188 (Eq.refl Bool.true)
  (allA_of_3_0 35 154 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 153 188 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 153 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 153 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 188 (accept_3_2 34 153 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 153 188 (Polychromatic418967fa.accept_14_5_13_6_1_3574 33 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 188
  (Polychromatic418967fa.accept_21_11_6_20_1_4589 32 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 153 188 (accept_3_2 31 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 153 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 153 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 188 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 188 (accept_3_2 28 153 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 188
  (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 153 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 188 (accept_3_2 25 153 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 153 188 (Polychromatic418967fa.accept_11_2_10_1_1_1017 24 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 188 (accept_3_2 22 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 188 (Polychromatic418967fa.accept_8_5_1_4_1_628 21 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 188 (Polychromatic418967fa.accept_11_9_10_1_1_581 20 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 188 (accept_3_2 19 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 153
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 153 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 188 (accept_3_2 16 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 153 188 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 153 188 (Polychromatic418967fa.accept_19_14_1_17_1_8063 14 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 188 (accept_3_2 13 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 153 188 (Polychromatic418967fa.accept_13_12_10_6_1_3212 12 153
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 188 (accept_3_2 10 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 188 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 188 (Polychromatic418967fa.accept_16_8_9_12_1_1737 8 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 188 (accept_3_2 7 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 153 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 188 (accept_3_2 4 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 188 (Polychromatic418967fa.accept_13_3_10_6_1_2382 3 153 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 188 (Polychromatic418967fa.accept_11_2_10_1_1_1017 2 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 188 (accept_3_2 1 153 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 188)))))))))))))))))))))))))))))))))))) (allB_succ' 37 152 188 (Eq.refl
  Bool.true) (allA_succ_of_gcd 36 152 188 4 9 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 152 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 188 2 17 76 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 188
  (Polychromatic418967fa.accept_13_7_9_6_1_148 33 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 188 4 8 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 152 188 (accept_3_2 31 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  152 188 2 15 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 152 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 152 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 188 4 7 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 188 (Polychromatic418967fa.accept_13_1_9_6_1_146
  27 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 152 188 2 13 76 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 152 188
  (accept_3_2 25 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 152 188 4 6 38 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 152 188
  (Polychromatic418967fa.accept_13_10_9_6_1_1026 23 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 152 188 2 11 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 152 188 (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 152 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 152 188 4 5 38 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 152 188 (accept_3_2 19 152 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 152 188 2 9 76 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 152 188
  (Polychromatic418967fa.accept_13_4_9_6_1_2376 17 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 152 188 4 4 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 152 188 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 152 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 188 2 7 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 188 (accept_3_2 13 152 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 188 4 3 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 188 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 152 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 188 2 5 76 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 188
  (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 188 4 2 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 188 (accept_3_2 7 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  188 2 3 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 188 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 152 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 188 4 1 38 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 152 188 (Polychromatic418967fa.accept_13_3_9_6_1_502 3 152 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 188 2 1 76 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 188 (accept_3_2 1 152 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 188))))))))))))))))))))))))))))))))))))) (allB_succ' 38 151 188 (Eq.refl Bool.true)
  (allA_of_3_0 38 151 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 150 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 38 150 188 2 19 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 188 (accept_3_2 37 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 188 2 18 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 188 (Polychromatic418967fa.accept_13_9_7_6_1_1673 35 150 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 188 2 17 75 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 188
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 188 2 16 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 188 (accept_3_2 31 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 188 2 15 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 29 150 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 188 2 14 75 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 188
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 188 2 13 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 188 (accept_3_2 25 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 188 2 12 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 150 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 188 2 11 75 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 188
  (Polychromatic418967fa.accept_9_3_6_8_1_308 21 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 188 2 10 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 188 (accept_3_2 19 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 188 2 9 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 188 (Polychromatic418967fa.accept_11_6_7_1_1_564 17 150 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 188 2 8 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 188 (Polychromatic418967fa.accept_12_3_6_8_1_969
  15 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 150 188 2 7 75 94
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 188
  (accept_3_2 13 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 188 2 6 75 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 150 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 188 2 5 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 150 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 150 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 150 188 2 4 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 188 (accept_3_2 7 150 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 150 188 2 3 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 150 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 5 150 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 188 2 2 75 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 150 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3
  150 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 188 2 1 75 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 188 (accept_3_2 1
  150 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150 188))))))))))))))))))))))))))))))))))))))) (allB_succ'
  40 149 188 (Eq.refl Bool.true) (allA_succ_of_accept 39 149 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 149 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 188
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 188 (accept_3_2 37 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 188 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 149 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 188 (accept_3_2 34 149 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 188
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 188 (accept_3_2 31 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 30 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 188 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 149 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 188 (accept_3_2 28 149 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 149 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 188
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 188 (accept_3_2 25 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 188 (Polychromatic418967fa.accept_16_7_5_12_1_4824 23 149 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 188 (accept_3_2 22 149 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 20 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 188 (accept_3_2 19 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 188 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 188 (accept_3_2 16 149 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 188
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 188 (accept_3_2 13 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 12 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 188 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 149 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 188 (accept_3_2 10 149 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 188
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 188 (accept_3_2 7 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 6 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 188 (Polychromatic418967fa.accept_11_5_6_1_1_988 5 149 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 188 (accept_3_2 4 149 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 2 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 188 (accept_3_2 1 149 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  188)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 148 188 (Eq.refl Bool.true) (allA_of_3_0 41 148 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 147 188 (Eq.refl Bool.true) (allA_succ_of_accept 41 147 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 188 (accept_3_2 40 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 39 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 38 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 188 (accept_3_2 37 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 188 (Polychromatic418967fa.accept_13_10_4_6_1_3224 36 147 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 188 (accept_3_2 34 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 33 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 32 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 188 (accept_3_2 31 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 188 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 147 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 188 (accept_3_2 28 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 188 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 188 (Polychromatic418967fa.accept_15_11_12_8_1_739 26 147 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 188 (accept_3_2 25 147 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 24 147 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 188 (accept_3_2 22 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 188 (Polychromatic418967fa.accept_19_2_14_17_1_700 21 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 20 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 188 (accept_3_2 19 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 188 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 147 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 188 (accept_3_2 16 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 188 (Polychromatic418967fa.accept_8_7_3_4_1_404 15 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 188 (Polychromatic418967fa.accept_9_5_3_8_1_316 14 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 188 (accept_3_2 13 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 188 (Polychromatic418967fa.accept_18_12_3_8_1_6817 12 147 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 188 (accept_3_2 10 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 188 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 188 (Polychromatic418967fa.accept_11_8_4_1_1_1000 8 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 188 (accept_3_2 7 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 188 (Polychromatic418967fa.accept_9_6_3_8_1_595 6 147 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 188 (accept_3_2 4 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 188 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 147 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 188 (Polychromatic418967fa.accept_9_2_3_8_1_318 2 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 188 (accept_3_2 1 147 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 188)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 146 188 (Eq.refl
  Bool.true) (allA_succ_of_gcd 42 146 188 2 21 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 146 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 41 146 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 188 2 20 73 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 39 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 188 2 19 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 188 (accept_3_2 37 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 188 2 18 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 188 (Polychromatic418967fa.accept_11_2_3_1_1_244 35 146 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 188 2 17 73 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 188
  (Polychromatic418967fa.accept_9_6_2_8_1_592 33 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 188 2 16 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 188 (accept_3_2 31 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 188 2 15 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 146 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 188 2 14 73 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 188
  (Polychromatic418967fa.accept_13_1_3_6_1_158 27 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 188 2 13 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 188 (accept_3_2 25 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 188 2 12 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 23 146 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 188 2 11 73 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 188
  (Polychromatic418967fa.accept_9_3_2_8_1_108 21 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 188 2 10 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 188 (accept_3_2 19 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 188 2 9 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 188 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 146 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 188 2 8 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 188 (Polychromatic418967fa.accept_9_6_2_8_1_592 15
  146 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 146 188 2 7 73 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 146 188 (accept_3_2 13
  146 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 146 188 2 6 73 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 146 188
  (Polychromatic418967fa.accept_12_11_2_8_1_511 11 146 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 146 188 2 5 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 146 188 (Polychromatic418967fa.accept_13_9_3_6_1_1661 9 146 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 188 2 4 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 188 (accept_3_2 7 146 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 146 188 2 3 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 146 188 (Polychromatic418967fa.accept_9_5_2_8_1_109 5 146 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 188 2 2 73 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 188 (Polychromatic418967fa.accept_9_3_2_8_1_108 3
  146 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 188 2 1 73 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 188 (accept_3_2 1
  146 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 188)))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 44 145 188 (Eq.refl Bool.true) (allA_of_3_0 44 145 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 45 144 188 (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 188 4 11 36 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 188 (accept_3_2 43 144 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 188 2 21 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 188 (Polychromatic418967fa.accept_13_2_1_6_1_2365
  41 144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 188 4 10 36 47
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 188
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 188 2 19 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 188 (accept_3_2 37 144 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 188 4 9 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 188 (Polychromatic418967fa.accept_13_9_1_6_1_510 35 144 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 188 2 17 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 33
  144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 144 188 4 8 36 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 188 (accept_3_2 31
  144 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 188 2 15 72 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 188
  (Polychromatic418967fa.accept_10_9_4_8_1_741 29 144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 144 188 4 7 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 144 188 (Polychromatic418967fa.accept_19_8_11_17_1_9503 27 144 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 188 2 13 72 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 188 (accept_3_2 25 144 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 188 4 6 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 188 2 11 72 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 188
  (Polychromatic418967fa.accept_13_8_1_6_1_997 21 144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 188 4 5 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 144 188 (accept_3_2 19 144 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  144 188 2 9 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 144 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 144 188 4 4 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 144 188 (Polychromatic418967fa.accept_13_2_1_6_1_2365 15 144 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 188 2 7 72 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 188 (accept_3_2 13 144 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 188 4 3 36 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 188
  (Polychromatic418967fa.accept_17_11_8_1_1_3362 11 144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 188 2 5 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 144 188 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 144 188 4 2 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 144 188 (accept_3_2 7 144 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 144 188 2 3 72 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 144 188 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 188 4 1 36 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 144 188 (Polychromatic418967fa.accept_7_3_4_6_1_329 3
  144 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 188 2 1 72 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 188 (accept_3_2 1
  144 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144 188)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 143 188 (Eq.refl Bool.true) (allA_succ_of_accept 45 143 188 (Polychromatic418967fa.accept_6_3_5_2_1_12
  45 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 188
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 188 (accept_3_2 43 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 188 (Polychromatic418967fa.accept_17_8_7_1_1_4521 42 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 188 (Polychromatic418967fa.accept_10_1_3_8_1_136 41 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 188 (accept_3_2 40 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 188
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 188 (accept_3_2 37 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 188 (Polychromatic418967fa.accept_8_3_7_4_1_42 35 143 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 188 (accept_3_2 34 143 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 188 (accept_3_2 31 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 188 (Polychromatic418967fa.accept_16_13_15_12_1_1748 29 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 188 (accept_3_2 28 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 188
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 188 (accept_3_2 25 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 188 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 143 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 188 (accept_3_2 22 143 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 188
  (Polychromatic418967fa.accept_16_4_15_12_1_1745 20 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 143 188 (accept_3_2 19 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 143 188 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 143 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 188 (Polychromatic418967fa.accept_25_17_18_13_1_10808 17
  143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 188 (accept_3_2 16
  143 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 188
  (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 143 188 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 143 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 188 (accept_3_2 13 143 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 143 188 (Polychromatic418967fa.accept_19_12_10_17_1_5189 12 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 188
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 188 (accept_3_2 10 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 188 (Polychromatic418967fa.accept_16_8_15_12_1_1747 8 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 188 (accept_3_2 7 143 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 188 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 143 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 188
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 188 (accept_3_2 4 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 188 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 188 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 143 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 188 (accept_3_2 1 143 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 188)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 142 188 (Eq.refl
  Bool.true) (allA_of_3_0 47 142 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 141 188 (Eq.refl Bool.true)
  (allA_succ_of_gcd 47 141 188 47 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 46 141 188 (accept_3_2 46 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 188 (Polychromatic418967fa.accept_22_1_9_12_1_10807 45 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 188 (accept_3_2 43 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 141 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 188 (accept_3_2 40 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 39 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 38 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 188 (accept_3_2 37 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 188 (Polychromatic418967fa.accept_16_4_13_12_1_1740 36 141 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 188 (accept_3_2 34 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 32 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 188 (accept_3_2 31 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 141 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 188 (accept_3_2 28 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 188 (Polychromatic418967fa.accept_20_7_1_8_1_10806 27 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 188 (accept_3_2 25 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 188 (Polychromatic418967fa.accept_16_8_13_12_1_3809 24 141 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 188 (accept_3_2 22 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 21 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 188 (Polychromatic418967fa.accept_9_2_6_8_1_321 20 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 188 (accept_3_2 19 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 141 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 188 (accept_3_2 16 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 188 (Polychromatic418967fa.accept_16_15_13_12_1_1787 15 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 188 (Polychromatic418967fa.accept_9_5_6_8_1_101 14 141 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 188 (accept_3_2 13 141 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 188 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 188 (accept_3_2 10 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 188 (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 141 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 188 (accept_3_2 7 141 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 188 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 141 188
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 188
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 188 (accept_3_2 4 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 188 (Polychromatic418967fa.accept_9_3_6_8_1_308 3 141 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 188 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 188 (accept_3_2 1 141 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141 188)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 140 188 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 140 188 4 12 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 140 188 (Polychromatic418967fa.accept_9_2_5_8_1_11 47 140 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 188 2 23 70 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 188
  (Polychromatic418967fa.accept_22_1_8_12_1_5938 45 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 140 188 4 11 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 140 188 (accept_3_2 43 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 188 2 21 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 188 (Polychromatic418967fa.accept_13_2_10_6_1_1676 41 140 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 188 4 10 35 47 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 39 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 188 2 19 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 188 (accept_3_2 37 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 188 4 9 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 140 188 (Polychromatic418967fa.accept_13_9_10_6_1_1028 35 140 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 188 2 17 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 33
  140 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 188 4 8 35 47 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 188 (accept_3_2 31
  140 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 188 2 15 70 94 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 29 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 188 4 7 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 140 188 (Polychromatic418967fa.accept_15_12_5_8_1_5247 27 140 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 188 2 13 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 140 188 (accept_3_2 25 140 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 140 188 4 6 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 188 (Polychromatic418967fa.accept_18_5_14_8_1_2966 23 140
  188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 188 2 11 70 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 188
  (Polychromatic418967fa.accept_9_3_5_8_1_99 21 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 188 4 5 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 140 188 (accept_3_2 19 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  140 188 2 9 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 140 188 (Polychromatic418967fa.accept_13_4_10_6_1_989 17 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 140 188 4 4 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 140 188 (Polychromatic418967fa.accept_9_6_5_8_1_598 15 140 188 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 188 2 7 70 94 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 188 (accept_3_2 13 140 188
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 188 4 3 35 47 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 188
  (Polychromatic418967fa.accept_9_2_5_8_1_11 11 140 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 188 2 5 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 140 188 (Polychromatic418967fa.accept_13_9_10_6_1_1028 9 140 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 188 4 2 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 188 (accept_3_2 7 140 188 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 140 188 2 3 70 94 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 140 188 (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 140 188 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 188 4 1 35 47 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 188 (Polychromatic418967fa.accept_9_3_5_8_1_99 3
  140 188 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 188 2 1 70 94 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 188 (accept_3_2 1
  140 188 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 188)))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_188_segment_000))))))))))))))))))))))))))))))))))))))))))))))))


