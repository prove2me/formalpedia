-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch174
-- name    : Polychromatic418967fa_Branch174
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:18:05.511082+00:00
-- url     : https://prove2.me/theorems/2650c93d-3bba-42ca-8b15-ebd561b9df8c
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch174_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_174 : allB 174 174 :=
  allB_succ' 2 173 174 (Eq.refl Bool.true) (allA_succ_of_accept 1 173 174 (accept_3_4 1 173 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 174)) (allB_succ' 3 172 174 (Eq.refl Bool.true) (allA_succ_of_gcd 2 172 174 2 1 86
  87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 174
  (Polychromatic418967fa.accept_13_1_3_5_1_140 1 172 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 172 174))) (allB_succ' 4 171 174 (Eq.refl Bool.true) (allA_succ_of_gcd 3 171 174 3 1 57 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 174
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 171 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171 174)))) (allB_succ' 5 170 174 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  170 174 2 2 85 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 170 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 170 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 170 174 2 1 85 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 170 174 (accept_3_4 1 170 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  174))))) (allB_succ' 6 169 174 (Eq.refl Bool.true) (allA_succ_of_accept 5 169 174 (accept_3_5 5 169 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 169 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 174 (accept_3_5 2 169 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 169 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 174)))))) (allB_succ' 7 168 174 (Eq.refl Bool.true) (allA_succ_of_gcd 6 168 174 6 1 28 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 174
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 168 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 168 174 2 2 84 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 168 174 3 1 56 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 168 174 2 1 84 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 168 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 168 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 174))))))) (allB_succ' 8 167 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 167 174 (accept_3_4 7 167 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 167 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 174 (accept_3_4 4 167 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 174 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 167 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 167 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 174 (accept_3_4 1 167 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  174)))))))) (allB_succ' 9 166 174 (Eq.refl Bool.true) (allA_succ_of_gcd 8 166 174 2 4 83 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 174
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 166 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 174 2 3 83 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 174 (accept_3_5 5 166 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  174 2 2 83 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 174 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 166 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 174 2 1 83 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 166 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 166 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 174))))))))) (allB_succ' 10 165 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 165 174 3 3 55 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 165 174 (Polychromatic418967fa.accept_12_8_9_6_1_127 8 165 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 174 3 2 55 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 165 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 174 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 165 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 174 3 1 55 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 165 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 174
  (Polychromatic418967fa.accept_10_1_5_4_1_276 1 165 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 165 174)))))))))) (allB_succ' 11 164 174 (Eq.refl Bool.true) (allA_succ_of_gcd 10 164 174 2 5 82 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 174
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 164 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 174 2 4 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 174 (accept_3_4 7 164 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  174 2 3 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 164 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 174 2 2 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 164 174 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 164 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 174 2 1 82 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 174 (accept_3_4 1 164 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 174))))))))))) (allB_succ' 12 163 174 (Eq.refl Bool.true) (allA_succ_of_accept 11
  163 174 (accept_3_5 11 163 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 174
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 163 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 163 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 163 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 174 (accept_3_5 8 163 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 163 174 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 163 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 174 (Polychromatic418967fa.accept_9_6_1_3_1_191 6
  163 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 174 (accept_3_5 5 163
  174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 163 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 163 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 163 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 174 (accept_3_5 2 163 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 163 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 163 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 174)))))))))))) (allB_succ' 13 162 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 162 174 6 2 27 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 162 174 (Polychromatic418967fa.accept_13_11_6_5_1_2339 11 162 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 174 2 5 81 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 162 174 3 3 54 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 162 174 2 4 81 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 162 174 (Polychromatic418967fa.accept_10_7_2_4_1_569 7
  162 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 174 6 1 27 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 162 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 162 174 2 2 81 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 162 174 3 1 54 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 162 174 2 1 81 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 162 174 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1 162 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 162 174))))))))))))) (allB_succ' 14 161 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 161 174 (accept_3_4 13 161 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 174 (Polychromatic418967fa.accept_17_12_8_4_1_2518 12 161 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 174 (accept_3_4 10 161 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 174 (Polychromatic418967fa.accept_18_9_17_12_1_462 9 161 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 174
  (Polychromatic418967fa.accept_14_8_7_6_1_1159 8 161 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 174 (accept_3_4 7 161 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 161 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 174 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 161 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 174 (accept_3_4 4 161 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 161 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 174 (accept_3_4 1 161 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  174)))))))))))))) (allB_succ' 15 160 174 (Eq.refl Bool.true) (allA_succ_of_gcd 14 160 174 2 7 80 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 174
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 160 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 174 2 6 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 160 174 (accept_3_5 11 160 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  160 174 2 5 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 160 174 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 160 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 160 174 2 4 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 160 174 (Polychromatic418967fa.accept_21_7_13_6_1_349 7 160 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 174 2 3 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 174 (accept_3_5 5 160 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 174 2 2 80 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 160 174 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 160 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 174 2 1 80 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 174
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 160 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 174))))))))))))))) (allB_succ' 16 159 174 (Eq.refl Bool.true) (allA_succ_of_gcd 15 159 174 3 5 53 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 159 174
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 159 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 159 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 174 3 4 53 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  159 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 159 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 159 174 3 3 53 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 159 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 159 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 174 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 159 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 159 174 3 2 53 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 159 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 159 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 174 3 1 53 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 174 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 159 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 159 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 159 174)))))))))))))))) (allB_succ' 17 158 174 (Eq.refl Bool.true) (allA_succ_of_gcd 16 158 174 2 8 79 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 174
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 158 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 174 2 7 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 158 174 (accept_3_4 13 158 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  158 174 2 6 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 158 174 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 158 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 158 174 2 5 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 158 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 158 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 174 2 4 79 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 174 (accept_3_4 7 158 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158 174 2 3 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 158 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 158 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 174 2 2 79 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 174
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 158 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 158 174 2 1 79 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 158 174 (accept_3_4 1 158 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  174))))))))))))))))) (allB_succ' 18 157 174 (Eq.refl Bool.true) (allA_succ_of_accept 17 157 174 (accept_3_5 17 157 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 16
  157 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 174 (accept_3_5 14 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 174 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 174 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 157 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 174 (accept_3_5 11 157 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 157 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 174
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 174 (accept_3_5 8 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 157 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 174 (accept_3_5 5 157 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 157 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 174 (accept_3_5 2 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 157 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 174)))))))))))))))))) (allB_succ' 19 156 174 (Eq.refl Bool.true) (allA_succ_of_gcd 18 156
  174 6 3 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  156 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 156 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 156 174 2 8 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 174 3 5 52 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 174 2 7 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 156 174 (Polychromatic418967fa.accept_17_13_3_4_1_2537 13 156 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 174 6 2 26 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 156 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 174 2 5 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 156 174 3 3 52 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 156 174 2 4 78 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 174 (Polychromatic418967fa.accept_11_7_2_9_1_480 7 156 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 174 6 1 26 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 174 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 156 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 174 2 2 78 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 174 3 1 52 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 174 2 1 78 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 174
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 174))))))))))))))))))) (allB_succ' 20 155 174 (Eq.refl Bool.true) (allA_succ_of_accept 19 155 174
  (accept_3_4 19 155 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 174
  (Polychromatic418967fa.accept_15_3_5_9_1_764 18 155 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 155 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 174 (accept_3_4 16 155 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 155 174 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 155 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 174 (Polychromatic418967fa.accept_9_5_2_3_1_194
  14 155 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 174 (accept_3_4 13
  155 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 155 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 155 174 (Polychromatic418967fa.accept_10_1_5_4_1_276 11 155 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 174 (accept_3_4 10 155 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 155 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 174 (Polychromatic418967fa.accept_9_8_2_3_1_447 8
  155 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 174 (accept_3_4 7 155
  174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 174
  (Polychromatic418967fa.accept_9_6_2_3_1_771 6 155 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 155 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 174 (accept_3_4 4 155 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 155 174 (Polychromatic418967fa.accept_15_3_5_9_1_764 3 155 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 2
  155 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 174 (accept_3_4 1 155
  174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155 174)))))))))))))))))))) (allB_succ' 21 154 174 (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 154 174 2 10 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 154 174 (Polychromatic418967fa.accept_13_6_11_5_1_133 19 154 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 154 174 2 9 77 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 154 174 (accept_3_5 17 154 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 154 174 2 8 77 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 154 174
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 154 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 154 174 2 7 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 154 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 154 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 174 2 6 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 174 (accept_3_5 11 154 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 174 2 5 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 174 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 154 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 154 174 2 4 77 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 154 174
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 154 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 154 174 2 3 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 154 174 (accept_3_5 5 154 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 154
  174 2 2 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  154 174 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 154 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 154 174 2 1 77 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 154 174 (Polychromatic418967fa.accept_19_1_2_3_1_6995 1 154 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 174))))))))))))))))))))) (allB_succ' 22 153 174 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 153 174 3 7 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 153 174 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 153 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 19
  153 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 174 3 6 51 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 174
  (Polychromatic418967fa.accept_10_7_3_4_1_978 17 153 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 174 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 153 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 174 3 5 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 174 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 153 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 174
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 13 153 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 174 3 4 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 174 (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 153
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 174 3 3 51 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 174
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 153 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 153 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 174 3 2 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 174 (Polychromatic418967fa.accept_14_5_13_6_1_3574 5 153 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 174
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 153 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 174 3 1 51 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 174 (Polychromatic418967fa.accept_12_2_9_6_1_439 2 153 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 174 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 153 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153 174)))))))))))))))))))))) (allB_succ' 23
  152 174 (Eq.refl Bool.true) (allA_succ_of_gcd 22 152 174 2 11 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 174 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 152 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 152 174 2 10 76 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 152 174 (accept_3_4 19
  152 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 152 174 2 9 76 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 152 174
  (Polychromatic418967fa.accept_10_7_2_4_1_569 17 152 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 152 174 2 8 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 152 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 152 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 174 2 7 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 174 (accept_3_4 13 152 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 174 2 6 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 152 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 174 2 5 76 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 174
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 152 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 174 2 4 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 174 (accept_3_4 7 152 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  174 2 3 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 174 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 152 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 174 2 2 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 152 174 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 152 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 174 2 1 76 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 174 (accept_3_4 1 152 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 152 174))))))))))))))))))))))) (allB_succ' 24 151 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 151 174 (accept_3_5 23 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 151 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 151 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 151 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 174 (accept_3_5 20 151 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 151 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 174
  (Polychromatic418967fa.accept_21_18_4_6_1_6697 18 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 151 174 (accept_3_5 17 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 151 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 151 174 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 151 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 174 (accept_3_5 14 151 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 151 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 151 174 (accept_3_5 11 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 151 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 151 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 151 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 174 (accept_3_5 8 151 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 174 (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 151 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 174
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 174 (accept_3_5 5 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 151 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 151 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 174 (accept_3_5 2 151 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 151 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 174)))))))))))))))))))))))) (allB_succ' 25 150 174
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 174 6 4 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 150 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 150 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 174 2 11 75 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 150 174 3 7 50 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 150 174 2 10 75 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 150 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 150 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 174 6 3 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 150 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 174 2 8 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 150 174 3 5 50 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 150 174 2 7 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 150 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 13
  150 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 174 6 2 25 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 174
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 150 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 150 174 2 5 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 150 174 3 3 50 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 150 174 2 4 75 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 174 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 150 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 174 6 1 25 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 150 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 174 2 2 75 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 174 3 1 50 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 174 2 1 75 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 150 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 174))))))))))))))))))))))))) (allB_succ' 26 149 174 (Eq.refl Bool.true) (allA_succ_of_accept 25 149 174
  (accept_3_4 25 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 174
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 149 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 174 (accept_3_4 22 149 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 149 174 (Polychromatic418967fa.accept_15_6_14_9_1_1471 21 149 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 174 (accept_3_4 19 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 174 (accept_3_4 16 149 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 174
  (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 174 (accept_3_4 13 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 174 (Polychromatic418967fa.accept_13_12_6_5_1_2335 12 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 174 (accept_3_4 10 149 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 174 (Polychromatic418967fa.accept_16_9_5_14_1_6126 9 149 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 174
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 174 (accept_3_4 7 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 174 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 149 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 174 (accept_3_4 4 149 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 174 (accept_3_4 1 149 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  174)))))))))))))))))))))))))) (allB_succ' 27 148 174 (Eq.refl Bool.true) (allA_succ_of_gcd 26 148 174 2 13 74 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 148 174
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 148 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 148 174 2 12 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 148 174 (accept_3_5 23 148 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 148 174 2 11 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 148 174 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 148 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 148 174 2 10 74 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 148 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 148 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 148 174 2 9 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 148 174 (accept_3_5 17 148 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  148 174 2 8 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 148 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 148 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 148 174 2 7 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 148 174 (Polychromatic418967fa.accept_20_13_8_14_1_1467 13 148 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 148 174 2 6 74 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 148 174 (accept_3_5 11
  148 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 148 174 2 5 74 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 148 174
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 148 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 148 174 2 4 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 148 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 148 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 174 2 3 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 174 (accept_3_5 5 148 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 148 174 2 2 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 148 174 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 148 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 174 2 1 74 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  148 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 174)))))))))))))))))))))))))))
  (allB_succ' 28 147 174 (Eq.refl Bool.true) (allA_succ_of_gcd 27 147 174 3 9 49 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 174
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 147 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 147 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 174 3 8 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 174 (Polychromatic418967fa.accept_10_3_7_4_1_584
  23 147 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 174
  (Polychromatic418967fa.accept_10_2_7_4_1_967 22 147 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 147 174 3 7 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 147 174 (Polychromatic418967fa.accept_12_8_3_6_1_909 20 147 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 174 (Polychromatic418967fa.accept_13_6_4_5_1_2330 19 147
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 174 3 6 49 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 174 (Polychromatic418967fa.accept_12_4_3_6_1_879 16 147 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 174 3 5 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 174 (Polychromatic418967fa.accept_12_2_3_6_1_112
  14 147 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 147 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 147 174 3 4 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 147 174 (Polychromatic418967fa.accept_10_1_7_4_1_968 11 147 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 174 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 147
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 174 3 3 49 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 174
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 147 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 174 (Polychromatic418967fa.accept_18_7_3_12_1_3241 7 147 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 174 3 2 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 174
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 147 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 174 3 1 49 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 174 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 147 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 147 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147 174)))))))))))))))))))))))))))) (allB_succ'
  29 146 174 (Eq.refl Bool.true) (allA_succ_of_gcd 28 146 174 2 14 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 174 (Polychromatic418967fa.accept_12_3_2_6_1_138
  27 146 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 146 174 2 13 73 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 146 174
  (accept_3_4 25 146 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 146 174 2 12 73 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 146 174
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 146 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 146 174 2 11 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 146 174 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 146 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 146 174 2 10 73 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 146 174 (accept_3_4 19 146 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 146 174 2 9 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 146 174 (Polychromatic418967fa.accept_9_8_2_3_1_447 17
  146 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 174 2 8 73 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 174
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 146 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 174 2 7 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 146 174 (accept_3_4 13 146 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  146 174 2 6 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 146 174 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 146 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 146 174 2 5 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 146 174 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 146 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 174 2 4 73 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 174 (accept_3_4 7 146 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146 174 2 3 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 146 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 146 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 174 2 2 73 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 174
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 146 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 146 174 2 1 73 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 146 174 (accept_3_4 1 146 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  174))))))))))))))))))))))))))))) (allB_succ' 30 145 174 (Eq.refl Bool.true) (allA_succ_of_gcd 29 145 174 29 1 5 6
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 28 145 174
  (Polychromatic418967fa.accept_19_9_12_3_1_2950 28 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 145 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 145 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 174 (accept_3_5 26 145 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 145 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 145 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 145 174 (Polychromatic418967fa.accept_9_6_1_3_1_191
  24 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 174 (accept_3_5 23
  145 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 174
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 145 174 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 145 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 174 (accept_3_5 20 145 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 145 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 145 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 145 174 (Polychromatic418967fa.accept_7_4_5_6_1_344
  18 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 174 (accept_3_5 17
  145 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 174
  (Polychromatic418967fa.accept_9_7_1_3_1_443 16 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 145 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 145 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 174 (accept_3_5 14 145 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 145 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 145 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 174
  (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 174 (accept_3_5 11 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 145 174 (Polychromatic418967fa.accept_13_10_2_5_1_1633 10 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 145 174 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 145 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 174 (accept_3_5 8 145 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 145 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 174
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 145 174 (accept_3_5 5 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  145 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 145 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 145 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 145 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 174 (accept_3_5 2 145 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 174)))))))))))))))))))))))))))))) (allB_succ' 31 144
  174 (Eq.refl Bool.true) (allA_succ_of_gcd 30 144 174 6 5 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 174 (Polychromatic418967fa.accept_13_3_1_5_1_499 29 144 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 174 2 14 72 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 174 3 9 48 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 174 2 13 72 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 174
  (Polychromatic418967fa.accept_13_12_1_5_1_1650 25 144 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 174 6 4 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 144 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 174 2 11 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 174 3 7 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 174 2 10 72 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 144 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 174 6 3 24 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 144 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 174 2 8 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 174 3 5 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 174 2 7 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 174 (Polychromatic418967fa.accept_17_13_8_4_1_2514
  13 144 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 174 6 2 24 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 174
  (Polychromatic418967fa.accept_21_11_18_6_1_3521 11 144 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 144 174 2 5 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 144 174 3 3 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 144 174 2 4 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 144 174 (Polychromatic418967fa.accept_17_7_8_4_1_1520 7 144 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 174 6 1 24 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 144 174 2 2 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 144 174 3 1 48 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 144 174 2 1 72 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 144 174 (Polychromatic418967fa.accept_17_1_8_4_1_1519 1 144 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144 174))))))))))))))))))))))))))))))) (allB_succ' 32 143 174 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 143 174 (accept_3_4 31 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 143 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 143 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 174 (accept_3_4 28 143 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 174 (Polychromatic418967fa.accept_10_7_3_4_1_978
  27 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 174
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 26 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 143 174 (accept_3_4 25 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 143 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 143 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 143 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 174 (accept_3_4 22 143 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 21
  143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 174 (accept_3_4 19 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 174 (accept_3_4 16 143 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 143 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 174
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 174 (accept_3_4 13 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 174 (Polychromatic418967fa.accept_17_12_7_4_1_7231 12 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 143 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 174 (accept_3_4 10 143 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 174
  (Polychromatic418967fa.accept_17_8_7_4_1_8617 8 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 174 (accept_3_4 7 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 174 (accept_3_4 4 143 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 174 (Polychromatic418967fa.accept_15_3_8_9_1_795 3 143 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 174
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 174 (accept_3_4 1 143 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  174)))))))))))))))))))))))))))))))) (allB_succ' 33 142 174 (Eq.refl Bool.true) (allA_succ_of_gcd 32 142 174 2 16 71 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 174
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 142 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 174 2 15 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 174 (accept_3_5 29 142 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 174 2 14 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 174 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 142 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 174 2 13 71 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 142 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 142 174 2 12 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 142 174 (accept_3_5 23 142 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 174 2 11 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 174 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 142 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 174 2 10 71 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 174
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 142 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 174 2 9 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 174 (accept_3_5 17 142 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 174 2 8 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 142 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 174 2 7 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 142 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 174 2 6 71 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 174 (accept_3_5 11 142 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 174 2 5 71 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 174
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 142 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 174 2 4 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 174 (Polychromatic418967fa.accept_10_7_2_4_1_569 7 142 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 174 2 3 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 174 (accept_3_5 5 142 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 174 2 2 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 142 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 174 2 1 71 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 1
  142 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  174))))))))))))))))))))))))))))))))) (allB_succ' 34 141 174 (Eq.refl Bool.true) (allA_succ_of_gcd 33 141 174 3 11 47
  58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 174
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 141 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 174 3 10 47 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 174 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 141 174 3 9 47 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 141 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 141 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 174 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 141 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 174 3 8 47 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 141 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 174 3 7 47 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 174 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 19 141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 141 174 3 6 47 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 141 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 141 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 141 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 174 3 5 47 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 174
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 141 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 174 3 4 47 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 141 174 3 3 47 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 141 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 141 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 141 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 174 3 2 47 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 141 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 174 3 1 47 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 141 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 141 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 141 174)))))))))))))))))))))))))))))))))) (allB_succ' 35 140 174 (Eq.refl Bool.true) (allA_succ_of_gcd 34
  140 174 2 17 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 140 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 140 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 174 2 16 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 174 (accept_3_4 31 140 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 174 2 15 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 174 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 140 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 174 2 14 70 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 174
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 140 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 174 2 13 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 174 (accept_3_4 25 140 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 174 2 12 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 174 (Polychromatic418967fa.accept_19_4_7_3_1_2893 23 140 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 174 2 11 70 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 174
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 140 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 174 2 10 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 174 (accept_3_4 19 140 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 174 2 9 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 140 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 174 2 8 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 15
  140 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 174 2 7 70 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 174 (accept_3_4 13
  140 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 174 2 6 70 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 140 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 140 174 2 5 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 140 174 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 140 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 174 2 4 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 174 (accept_3_4 7 140 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 140 174 2 3 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 140 174 (Polychromatic418967fa.accept_19_5_7_3_1_6990 5 140 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 174 2 2 70 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 174 (Polychromatic418967fa.accept_12_3_8_6_1_895 3
  140 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 174 2 1 70 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 174 (accept_3_4 1
  140 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140 174))))))))))))))))))))))))))))))))))) (allB_succ' 36
  139 174 (Eq.refl Bool.true) (allA_succ_of_accept 35 139 174 (accept_3_5 35 139 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 139 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 139 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 139 174 (accept_3_5 32
  139 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 139 174
  (Polychromatic418967fa.accept_22_9_7_20_1_9833 31 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 139 174 (Polychromatic418967fa.accept_13_4_9_5_1_1641 30 139 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 174 (accept_3_5 29 139 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 139 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 139 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 174 (Polychromatic418967fa.accept_11_5_7_9_1_2696
  27 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 139 174 (accept_3_5 26
  139 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 139 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 139 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 139 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 174 (accept_3_5 23 139 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 139 174 (Polychromatic418967fa.accept_25_22_14_24_1_9832 22 139 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 174 (accept_3_5 20 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 174 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 139 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 174 (accept_3_5 17 139 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 139 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 174
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 174 (accept_3_5 14 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 174 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 139 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 174 (accept_3_5 11 139 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 139 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 9 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 174 (accept_3_5 8 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 139 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 174 (accept_3_5 5 139 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 174 (Polychromatic418967fa.accept_13_4_9_5_1_1641 4 139 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 174
  (Polychromatic418967fa.accept_10_3_9_4_1_960 3 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 174 (accept_3_5 2 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 139 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 174)))))))))))))))))))))))))))))))))))) (allB_succ' 37 138 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 138 174 6 6 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 138 174 (Polychromatic418967fa.accept_15_5_3_9_1_283 35 138 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 174 2 17 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 138 174 3 11 46 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 174 2 16 69 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 174
  (Polychromatic418967fa.accept_16_15_10_14_1_2872 31 138 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 138 174 6 5 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 138 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 138 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 174 2 14 69 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 174 3 9 46 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 174 2 13 69 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 174
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 138 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 174 6 4 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 174 (Polychromatic418967fa.accept_13_10_8_5_1_1616 23 138 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 174 2 11 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 174 3 7 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 174 2 10 69 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 174
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 138 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 174 6 3 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 174 (Polychromatic418967fa.accept_19_17_5_3_1_5455 17 138 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 174 2 8 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 174 3 5 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 174 2 7 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 174
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 13 138 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 138 174 6 2 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 138 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 138 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 174 2 5 69 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 138 174 3 3 46 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 138 174 2 4 69 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 174
  (Polychromatic418967fa.accept_16_7_10_14_1_1884 7 138 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 174 6 1 23 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 174 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 138 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 174 2 2 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 174 3 1 46 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 174 2 1 69 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 138 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138 174)))))))))))))))))))))))))))))))))))))
  (allB_succ' 38 137 174 (Eq.refl Bool.true) (allA_succ_of_accept 37 137 174 (accept_3_4 37 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 174 (Polychromatic418967fa.accept_16_4_9_14_1_3883 36 137 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 174 (accept_3_4 34 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 174 (accept_3_4 31 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 137 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 174
  (Polychromatic418967fa.accept_11_7_5_9_1_884 29 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 174 (accept_3_4 28 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 174 (accept_3_4 25 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 137 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 174 (accept_3_4 22 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 174 (Polychromatic418967fa.accept_10_1_7_4_1_968 21 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 174 (Polychromatic418967fa.accept_16_4_9_14_1_3883 20 137 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 174 (accept_3_4 19 137 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 174 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 137
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 174
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 174 (accept_3_4 16 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 174 (accept_3_4 13 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 137 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 174 (accept_3_4 10 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 174 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 174 (accept_3_4 7 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 174 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 137 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 174 (accept_3_4 4 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 174 (accept_3_4 1 137 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 174)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 136 174 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 136 174 2 19 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 136 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 136 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 174 2 18 68 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 174 (accept_3_5 35 136 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 174 2 17 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 174
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 136 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 136 174 2 16 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 136 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 136 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 174 2 15 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 174 (accept_3_5 29 136 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 174 2 14 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 174 (Polychromatic418967fa.accept_12_3_4_6_1_434
  27 136 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 174 2 13 68 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 174
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 136 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 174 2 12 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 136 174 (accept_3_5 23 136 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 136 174 2 11 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 136 174 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 136 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 174 2 10 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 174
  (Polychromatic418967fa.accept_27_19_1_12_1_3865 19 136 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 136 174 2 9 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 136 174 (accept_3_5 17 136 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 136 174 2 8 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 136 174 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 136 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 136 174 2 7 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 136 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  136 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 174 2 6 68 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 174 (accept_3_5 11
  136 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 174 2 5 68 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 174
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 136 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 136 174 2 4 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 136 174 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 136 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 136 174 2 3 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 136 174 (accept_3_5 5 136 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 136 174 2 2 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 136 174 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 136 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 136 174 2 1 68 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 136 174 (Polychromatic418967fa.accept_13_1_6_5_1_1610 1
  136 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  174))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 135 174 (Eq.refl Bool.true) (allA_succ_of_gcd 39 135 174 3
  13 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135
  174 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 135 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 174 3 12 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 135 174
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 35 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 135 174 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 135 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 174 3 11 45 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 135 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 135 174 3 10 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 135 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 29
  135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 174
  (Polychromatic418967fa.accept_11_6_3_9_1_906 28 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 174 3 9 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 174 (Polychromatic418967fa.accept_10_6_5_4_1_571 26 135 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 135 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 174 3 8 45 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 174
  (Polychromatic418967fa.accept_18_5_9_12_1_8461 23 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 135 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 174 3 7 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 174 (Polychromatic418967fa.accept_12_8_3_6_1_909
  20 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 174
  (Polychromatic418967fa.accept_10_9_5_4_1_966 19 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 135 174 3 6 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 135 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 174 (Polychromatic418967fa.accept_10_6_5_4_1_571 16 135
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 174 3 5 45 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 174
  (Polychromatic418967fa.accept_12_2_3_6_1_112 14 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 135 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 174 3 4 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 11
  135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 174
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 135 174 3 3 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 135 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 174 (Polychromatic418967fa.accept_21_7_9_6_1_8212 7 135 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 174 3 2 45 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 135 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 174 3 1 45 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 174 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 135 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 1 135 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 135 174)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 134 174 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 134 174 2 20 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 134 174 (Polychromatic418967fa.accept_12_3_2_6_1_138 39 134 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 134 174 2 19 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 134 174 (accept_3_4 37 134 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 134 174 2 18 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 134 174 (Polychromatic418967fa.accept_13_9_4_5_1_1651 35 134
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 174 2 17 67 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 134 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 174 2 16 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 174 (accept_3_4 31 134 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 174 2 15 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 174 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 134 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 174 2 14 67 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 174
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 134 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 174 2 13 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 174 (accept_3_4 25 134 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 174 2 12 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 134 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 174 2 11 67 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 174
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 134 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 174 2 10 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 174 (accept_3_4 19 134 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 174 2 9 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 174 (Polychromatic418967fa.accept_19_17_1_3_1_4160 17 134 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 174 2 8 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 15
  134 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 174 2 7 67 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 174 (accept_3_4 13
  134 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 174 2 6 67 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 134 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 174 2 5 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 134 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 174 2 4 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 174 (accept_3_4 7 134 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 174 2 3 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 134 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 174 2 2 67 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 174 (Polychromatic418967fa.accept_12_3_2_6_1_138 3
  134 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 174 2 1 67 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 174 (accept_3_4 1
  134 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134 174)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 133 174 (Eq.refl Bool.true) (allA_succ_of_accept 41 133 174 (accept_3_5 41 133 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 174 (accept_3_5 38 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 174 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 174 (accept_3_5 35 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 174 (Polychromatic418967fa.accept_13_8_3_5_1_1636 34 133
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 174
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 174 (accept_3_5 32 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 174 (Polychromatic418967fa.accept_17_13_14_4_1_2468 30 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 174 (accept_3_5 29 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 133 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 174 (accept_3_5 26 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 174 (Polychromatic418967fa.accept_16_9_5_14_1_6126 25 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 174 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 133 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 174 (accept_3_5 23 133 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 174
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 174 (accept_3_5 20 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 174 (Polychromatic418967fa.accept_15_3_13_9_1_3196 18 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 174 (accept_3_5 17 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 174 (Polychromatic418967fa.accept_21_16_7_6_1_6687 16 133
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 174 (accept_3_5 14 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 174 (Polychromatic418967fa.accept_21_12_7_6_1_3607 12 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 174 (accept_3_5 11 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 133 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 174
  (Polychromatic418967fa.accept_10_9_3_4_1_985 9 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 174 (accept_3_5 8 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 174 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 133 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 174 (accept_3_5 5 133 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 133 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 174 (accept_3_5 2 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 133 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 174)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 132 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 132 174 6 7 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 132 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 132 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 174 2 20 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 174 3 13 44 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 174 2 19 66 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 132 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 174 6 6 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 132 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 174 2 17 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 132 174 3 11 44 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 174 2 16 66 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 174
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 132 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 174 6 5 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 132 174 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 132 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 174 2 14 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 132 174 3 9 44 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 132 174 2 13 66 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 132 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 174 6 4 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 132 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 174 2 11 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 174 3 7 44 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 174 2 10 66 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 132 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 174 6 3 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 132 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 174 2 8 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 174 3 5 44 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 174 2 7 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 13
  132 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 174 6 2 22 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 132 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 174 2 5 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 132 174 3 3 44 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 132 174 2 4 66 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 174 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 132 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 174 6 1 22 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 132 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 174 2 2 66 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 174 3 1 44 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 174 2 1 66 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 132 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 174))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 131 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 131 174 (accept_3_4 43 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 174 (accept_3_4 40 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 131 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 174 (accept_3_4 37 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 131 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 174 (accept_3_4 34 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 174
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 174 (accept_3_4 31 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 174 (Polychromatic418967fa.accept_11_8_10_9_1_1401 30 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 174 (accept_3_4 28 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 174 (Polychromatic418967fa.accept_10_7_1_4_1_1447 27 131 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 174
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 174 (accept_3_4 25 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 174 (Polychromatic418967fa.accept_11_1_10_9_1_871 23 131 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 174 (accept_3_4 22 131 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 174 (accept_3_4 19 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 174 (accept_3_4 16 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 131 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 174
  (Polychromatic418967fa.accept_19_14_17_3_1_4137 14 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 174 (accept_3_4 13 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 174 (Polychromatic418967fa.accept_11_1_10_9_1_871 12 131 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 131 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 174 (accept_3_4 10 131 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 174
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 174 (accept_3_4 7 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 174 (accept_3_4 4 131 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 174 (Polychromatic418967fa.accept_13_3_1_5_1_499 3 131 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 174 (accept_3_4 1 131 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  174)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 130 174 (Eq.refl Bool.true) (allA_succ_of_gcd 44 130
  174 2 22 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  130 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 130 174 2 21 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 130 174 (accept_3_5 41 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 174 2 20 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 174 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 130 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 174 2 19 65 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 174
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 174 2 18 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 174 (accept_3_5 35 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 174 2 17 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 130 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 174 2 16 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 174
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 130 174 2 15 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 130 174 (accept_3_5 29 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 174 2 14 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 174 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 130 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 174 2 13 65 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 174
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 174 2 12 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 174 (accept_3_5 23 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 174 2 11 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 174 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 130 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 174 2 10 65 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 174 2 9 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 174 (accept_3_5 17 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 174 2 8 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 174 2 7 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 174 (Polychromatic418967fa.accept_19_13_16_3_1_6983 13 130 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 174 2 6 65 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 174 (accept_3_5 11
  130 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 174 2 5 65 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 174
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 130 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 174 2 4 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 130 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 174 2 3 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 174 (accept_3_5 5 130 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 174 2 2 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 130 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 174 2 1 65 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  130 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  174))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 129 174 (Eq.refl Bool.true) (allA_succ_of_gcd 45 129
  174 3 15 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44
  129 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 129 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 129 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 174 3 14 43 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 174
  (Polychromatic418967fa.accept_13_2_12_5_1_1602 41 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 174 (Polychromatic418967fa.accept_12_4_9_6_1_440 40 129 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 129 174 3 13 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 129 174 (Polychromatic418967fa.accept_10_8_9_4_1_961
  38 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 174
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 174 3 12 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 174
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 174 3 11 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 129 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 174 3 10 43 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 174
  (Polychromatic418967fa.accept_16_13_1_14_1_2855 29 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 129 174 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 129 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 174 3 9 43 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 174
  (Polychromatic418967fa.accept_12_2_9_6_1_439 26 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 129 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 174 3 8 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 174
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 129 174 3 7 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 174 (Polychromatic418967fa.accept_12_8_9_6_1_127 20 129 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 129 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 174 3 6 43 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 174
  (Polychromatic418967fa.accept_13_4_12_5_1_476 17 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 129 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 174 3 5 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 174 (Polychromatic418967fa.accept_12_2_9_6_1_439
  14 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 174
  (Polychromatic418967fa.accept_10_3_9_4_1_960 13 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 174 3 4 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 174 (Polychromatic418967fa.accept_11_10_8_9_1_492 10 129
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 174 3 3 43 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 174
  (Polychromatic418967fa.accept_10_8_9_4_1_961 8 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 129 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 174 3 2 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 174 (Polychromatic418967fa.accept_10_5_9_4_1_1420 5 129 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 174
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 129 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 174 3 1 43 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 129 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 174 (Polychromatic418967fa.accept_13_1_12_5_1_1601 1 129
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  174)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 128 174 (Eq.refl Bool.true) (allA_succ_of_gcd 46 128
  174 2 23 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45
  128 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 128 174 2 22 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 128 174 (accept_3_4 43 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 174 2 21 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 128 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 174 2 20 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 174 2 19 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 174 (accept_3_4 37 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 174 2 18 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 174 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 128 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 174 2 17 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 174
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 128 174 2 16 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 128 174 (accept_3_4 31 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 174 2 15 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 128 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 174 2 14 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 174
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 174 2 13 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 174 (accept_3_4 25 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 174 2 12 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 128 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 174 2 11 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 174
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 174 2 10 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 174 (accept_3_4 19 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 174 2 9 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 128 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 128 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 174 2 8 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  128 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 174 2 7 64 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 174 (accept_3_4 13
  128 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 174 2 6 64 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 128 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 128 174 2 5 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 128 174 (Polychromatic418967fa.accept_10_9_8_4_1_970 9 128 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 174 2 4 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 174 (accept_3_4 7 128 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 128 174 2 3 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 128 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 128 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 174 2 2 64 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 3
  128 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 174 2 1 64 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 174 (accept_3_4 1
  128 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128 174)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 127 174 (Eq.refl Bool.true) (allA_succ_of_accept 47 127 174 (accept_3_5 47 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 127 174 (Polychromatic418967fa.accept_15_1_7_9_1_20 46 127 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 127 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 45 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 127 174 (accept_3_5 44 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 127 174 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 127 174 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 127 174 (accept_3_5 41 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 127 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 127 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 127 174
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 39 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 127 174 (accept_3_5 38 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 127 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 174 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 127
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 127 174 (accept_3_5 35 127
  174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 127 174
  (Polychromatic418967fa.accept_9_7_1_3_1_443 34 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 127 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 174 (accept_3_5 32 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 127 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 174 (Polychromatic418967fa.accept_7_2_1_6_1_173
  30 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 127 174 (accept_3_5 29
  127 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 127 174
  (Polychromatic418967fa.accept_13_2_10_5_1_1643 28 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 127 174 (Polychromatic418967fa.accept_19_8_13_3_1_4172 27 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 174 (accept_3_5 26 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 127 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 174 (Polychromatic418967fa.accept_9_6_1_3_1_191
  24 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 127 174 (accept_3_5 23
  127 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 127 174
  (Polychromatic418967fa.accept_9_4_1_3_1_190 22 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 127 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 174 (accept_3_5 20 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 127 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 174 (Polychromatic418967fa.accept_17_1_8_4_1_1519
  18 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 127 174 (accept_3_5 17
  127 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 127 174
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 127 174 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 174 (accept_3_5 14 127 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 127 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 174 (Polychromatic418967fa.accept_7_5_1_6_1_163
  12 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 127 174 (accept_3_5 11
  127 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 127 174
  (Polychromatic418967fa.accept_16_10_15_14_1_1086 10 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 174 (accept_3_5 8 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 174 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 127 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 174
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 174 (accept_3_5 5 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 127 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 174 (Polychromatic418967fa.accept_10_3_7_4_1_584 3 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 174 (accept_3_5 2 127 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 127 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127 174))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 49 126 174 (Eq.refl Bool.true) (allA_succ_of_gcd 48 126 174 6 8 21 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 174
  (Polychromatic418967fa.accept_19_9_12_3_1_2950 47 126 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 126 174 2 23 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 126 174 3 15 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 174 2 22 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 174 (Polychromatic418967fa.accept_13_4_9_5_1_1641 43 126
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 174 6 7 21 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 174
  (Polychromatic418967fa.accept_13_2_9_5_1_959 41 126 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 126 174 2 20 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 126 174 3 13 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 174 2 19 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 174 (Polychromatic418967fa.accept_17_3_7_4_1_7230 37 126
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 126 174 6 6 21 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 126 174
  (Polychromatic418967fa.accept_10_5_6_4_1_64 35 126 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 126 174 2 17 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 126 174 3 11 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 174 2 16 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 174 (Polychromatic418967fa.accept_15_1_6_9_1_254 31 126 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 174 6 5 21 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 174
  (Polychromatic418967fa.accept_11_7_5_9_1_884 29 126 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 126 174 2 14 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 126 174 3 9 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 126 174 2 13 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 126 174 (Polychromatic418967fa.accept_10_5_6_4_1_64 25 126 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 174 6 4 21 29 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 174
  (Polychromatic418967fa.accept_25_23_1_24_1_7998 23 126 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 126 174 2 11 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 174 3 7 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 174 2 10 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 174 (Polychromatic418967fa.accept_15_4_6_9_1_2269 19 126
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 126 174 6 3 21 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 126 174
  (Polychromatic418967fa.accept_13_4_9_5_1_1641 17 126 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 126 174 2 8 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 126 174 3 5 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 126 174 2 7 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 126 174 (Polychromatic418967fa.accept_19_13_12_3_1_5540 13 126 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 174 6 2 21 29 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 174
  (Polychromatic418967fa.accept_15_11_6_9_1_3236 11 126 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 126 174 2 5 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 126 174 3 3 42 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 126 174 2 4 63 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 174 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 126 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 174 6 1 21 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 174 (Polychromatic418967fa.accept_10_5_6_4_1_64 5 126 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 174 2 2 63 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 174 3 1 42 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 174 2 1 63 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 174
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 1 126 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 174))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 125 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 125 174 (accept_3_4 49 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 174 (Polychromatic418967fa.accept_15_3_5_9_1_764 48 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 174 (accept_3_4 46 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 174 (Polychromatic418967fa.accept_17_11_6_4_1_4729 45 125 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 174
  (Polychromatic418967fa.accept_15_14_5_9_1_2284 44 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 174 (accept_3_4 43 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 174 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 174 (accept_3_4 40 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 125 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 174 (accept_3_4 37 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 174 (Polychromatic418967fa.accept_10_6_5_4_1_571 36 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 174 (accept_3_4 34 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 125 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 174
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 174 (accept_3_4 31 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 174 (Polychromatic418967fa.accept_20_10_5_14_1_8378 30 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 174 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 174 (accept_3_4 28 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 125 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 174
  (Polychromatic418967fa.accept_10_6_5_4_1_571 26 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 174 (accept_3_4 25 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 174 (accept_3_4 22 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 174 (Polychromatic418967fa.accept_10_1_5_4_1_276 21 125 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 174 (accept_3_4 19 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 174 (Polychromatic418967fa.accept_15_3_5_9_1_764 18 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 174 (Polychromatic418967fa.accept_16_1_13_14_1_1064 17 125 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 174 (accept_3_4 16 125 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 125 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 174
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 174 (accept_3_4 13 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 174 (Polychromatic418967fa.accept_13_12_8_5_1_976 12 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 174 (accept_3_4 10 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 174 (Polychromatic418967fa.accept_10_9_5_4_1_966 9 125 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 174
  (Polychromatic418967fa.accept_19_8_11_3_1_5539 8 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 174 (accept_3_4 7 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 174 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 174 (accept_3_4 4 125 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 125 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 174 (accept_3_4 1 125 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  174)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 124 174 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  124 174 2 25 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 124 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 124 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 124 174 2 24 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 124 174 (accept_3_5 47 124 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 124 174 2 23 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 124 174 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 124 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 174 2 22 62 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 174
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 174 2 21 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 174 (accept_3_5 41 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 174 2 20 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 124 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 174 2 19 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 174
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 174 2 18 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 124 174 (accept_3_5 35 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 124 174 2 17 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 124 174 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 124 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 174 2 16 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 174
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 124 174 2 15 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 124 174 (accept_3_5 29 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 124 174 2 14 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 124 174 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 124 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 124 174 2 13 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 124 174
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 124 174 2 12 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 124 174 (accept_3_5 23 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 124 174 2 11 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 124 174 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 124 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 124 174 2 10 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 124 174
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 124 174 2 9 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 124 174 (accept_3_5 17 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  124 174 2 8 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 124 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 124 174 2 7 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 124 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 124 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 124 174 2 6 62 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 124 174 (accept_3_5 11 124 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 124 174 2 5 62 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 124 174
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 124 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 124 174 2 4 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 124 174 (Polychromatic418967fa.accept_19_7_10_3_1_4149 7 124 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 174 2 3 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 174 (accept_3_5 5 124 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 124 174 2 2 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 124 174 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 124 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 174 2 1 62 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 1
  124 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  174))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 123 174 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  123 174 3 17 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 123 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 123 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 123 174 3 16 41 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 123 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 123 174 3 15 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 123 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 44
  123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 123 174 3 14 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 123 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 123 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 174 (Polychromatic418967fa.accept_7_5_4_6_1_167
  40 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 123 174 3 13 41 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 123 174
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 123 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 174 3 12 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 123 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 123 174 3 11 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 123 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 123 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 174 (Polychromatic418967fa.accept_7_3_4_6_1_329
  31 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 123 174 3 10 41 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 123 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 174 3 9 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 26
  123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 174
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 123 174 3 8 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 123 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 123 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 174 3 7 41 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 123 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 174 3 6 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 174
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 123 174 3 5 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 123 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 123 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 174 3 4 41 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 174 3 3 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 123 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 174 3 2 41 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 123 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 174 3 1 41 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 174
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 123 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 123 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123 174)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  122 174 (Eq.refl Bool.true) (allA_succ_of_gcd 52 122 174 2 26 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 122 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 122 174 2 25 61 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 122 174 (accept_3_4 49
  122 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 122 174 2 24 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 122 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 122 174 2 23 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 122 174 (Polychromatic418967fa.accept_12_9_2_6_1_455 45 122 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 122 174 2 22 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 122 174 (accept_3_4 43 122 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 122 174 2 21 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 122 174 (Polychromatic418967fa.accept_15_11_2_9_1_1480
  41 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 174 2 20 61 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 174
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 174 2 19 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 174 (accept_3_4 37 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 174 2 18 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 122 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 174 2 17 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 174
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 174 2 16 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 174 (accept_3_4 31 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 174 2 15 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 174 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 122 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 174 2 14 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 174
  (Polychromatic418967fa.accept_10_7_2_4_1_569 27 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 174 2 13 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 174 (accept_3_4 25 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 174 2 12 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 122 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 174 2 11 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 174
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 174 2 10 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 174 (accept_3_4 19 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 174 2 9 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 122 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 174 2 8 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 15
  122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 174 2 7 61 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 174 (accept_3_4 13
  122 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 174 2 6 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 174
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 174 2 5 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 122 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 174 2 4 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 174 (accept_3_4 7 122 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 174 2 3 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 174 (Polychromatic418967fa.accept_16_5_10_14_1_5074 5 122 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 174 2 2 61 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 174
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 122 174 2 1 61 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 122 174 (accept_3_4 1 122 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  174))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 121 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 53 121 174 (accept_3_5 53 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 174 (accept_3_5 50 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 174 (Polychromatic418967fa.accept_13_10_4_5_1_2331 49 121 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 174
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 48 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 174 (accept_3_5 47 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 174 (accept_3_5 44 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 121 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 174
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 174 (accept_3_5 41 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 174 (Polychromatic418967fa.accept_13_1_4_5_1_113 40 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 174 (accept_3_5 38 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 121 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 174
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 174 (accept_3_5 35 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 174 (accept_3_5 32 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 121 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 174
  (Polychromatic418967fa.accept_20_10_1_14_1_8359 30 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 121 174 (accept_3_5 29 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 121 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 121 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 121 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 174 (accept_3_5 26 121 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 174 (Polychromatic418967fa.accept_7_4_2_6_1_337
  25 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 174
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 174 (accept_3_5 23 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 174 (Polychromatic418967fa.accept_15_6_1_9_1_1476 21 121 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 174 (accept_3_5 20 121 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 121 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 174 (accept_3_5 17 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 174 (accept_3_5 14 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 174 (Polychromatic418967fa.accept_19_13_7_3_1_9798 13 121 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 174
  (Polychromatic418967fa.accept_13_12_4_5_1_1637 12 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 174 (accept_3_5 11 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 174 (Polychromatic418967fa.accept_13_9_4_5_1_1651 9 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 174 (accept_3_5 8 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 121 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 174
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 174 (accept_3_5 5 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 121 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 174 (accept_3_5 2 121 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  174)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 120 174 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 120 174 6 9 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 120 174 (Polychromatic418967fa.accept_13_1_3_5_1_140 53 120 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 174 2 26 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 120 174 3 17 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 174 2 25 60 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 174
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 49 120 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 174 6 8 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 120 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 120 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 174 2 23 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 174 3 15 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 174 2 22 60 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 174
  (Polychromatic418967fa.accept_19_5_6_3_1_5578 43 120 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 174 6 7 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 120 174 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 120 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 174 2 20 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 174 3 13 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 174 2 19 60 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 174
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 120 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 174 6 6 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 120 174 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 120 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 174 2 17 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 174 3 11 40 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 174 2 16 60 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 174
  (Polychromatic418967fa.accept_17_14_1_4_1_2485 31 120 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 174 6 5 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 174 (Polychromatic418967fa.accept_21_8_15_6_1_8247 29 120 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 174 2 14 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 174 3 9 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 174 2 13 60 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 174
  (Polychromatic418967fa.accept_17_8_1_4_1_9831 25 120 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 174 6 4 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 120 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 174 2 11 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 174 3 7 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 174 2 10 60 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 120 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 120 174 6 3 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 120 174 (Polychromatic418967fa.accept_19_17_6_3_1_9830 17 120 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 120 174 2 8 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 120 174 3 5 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 120 174 2 7 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 120 174
  (Polychromatic418967fa.accept_21_13_15_6_1_3556 13 120 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 120 174 6 2 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 120 174 (Polychromatic418967fa.accept_13_11_3_5_1_982 11 120 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 174 2 5 60 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 174 3 3 40 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 174 2 4 60 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 174
  (Polychromatic418967fa.accept_14_7_8_6_1_1164 7 120 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 174 6 1 20 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 120 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 174 2 2 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 174 3 1 40 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 174 2 1 60 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 174 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 120 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  174))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 119 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 119 174 (accept_3_4 55 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 174 (Polychromatic418967fa.accept_19_16_5_3_1_1813 54 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 174 (accept_3_4 52 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 174 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 174
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 174 (accept_3_4 49 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 174 (Polychromatic418967fa.accept_10_8_9_4_1_961 48 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 174 (Polychromatic418967fa.accept_16_15_7_14_1_2883 47 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 174 (accept_3_4 46 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 119 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 174
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 174 (accept_3_4 43 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 174 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 174 (accept_3_4 40 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 174 (Polychromatic418967fa.accept_19_1_5_3_1_6970 39 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 174
  (Polychromatic418967fa.accept_10_8_9_4_1_961 38 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 174 (accept_3_4 37 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 174 (Polychromatic418967fa.accept_13_10_2_5_1_1633 36 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 174 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 174 (accept_3_4 34 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 174
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 174 (accept_3_4 31 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 174 (Polychromatic418967fa.accept_13_4_2_5_1_4045 30 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 174 (accept_3_4 28 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 174 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 119 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 174
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 174 (accept_3_4 25 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 174 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 174 (accept_3_4 22 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 174
  (Polychromatic418967fa.accept_13_7_2_5_1_2344 20 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 174 (accept_3_4 19 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 174 (Polychromatic418967fa.accept_10_8_9_4_1_961 18 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 174 (accept_3_4 16 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 174 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 174
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 174 (accept_3_4 13 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 174 (Polychromatic418967fa.accept_13_12_2_5_1_1634 12 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 174 (Polychromatic418967fa.accept_21_11_14_6_1_8311 11 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 174 (accept_3_4 10 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 119 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 174
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 174 (accept_3_4 7 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 174 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 174 (accept_3_4 4 119 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 174 (Polychromatic418967fa.accept_10_3_9_4_1_960 3 119 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 174
  (Polychromatic418967fa.accept_19_2_5_3_1_5536 2 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 174 (accept_3_4 1 119 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  174)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 118 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 118 174 2 28 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 118 174 (Polychromatic418967fa.accept_13_3_1_5_1_499 55 118 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 118 174 2 27 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 118 174 (accept_3_5 53 118 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 118 174 2 26 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 118 174 (Polychromatic418967fa.accept_9_6_1_3_1_191 51
  118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 174 2 25 59 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 174
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 174 2 24 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 174 (accept_3_5 47 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 174 2 23 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 174 (Polychromatic418967fa.accept_12_9_10_6_1_872 45 118 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 174 2 22 59 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 174
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 174 2 21 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 174 (accept_3_5 41 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 174 2 20 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 174 (Polychromatic418967fa.accept_10_9_8_4_1_970 39 118 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 174 2 19 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 174
  (Polychromatic418967fa.accept_15_7_13_9_1_1466 37 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 174 2 18 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 174 (accept_3_5 35 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 174 2 17 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 174 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 118 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 174 2 16 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 174
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 174 2 15 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 174 (accept_3_5 29 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 174 2 14 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 174 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 118 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 174 2 13 59 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 174
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 174 2 12 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 174 (accept_3_5 23 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 174 2 11 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 174 (Polychromatic418967fa.accept_11_10_8_9_1_492 21 118 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 174 2 10 59 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 174
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 174 2 9 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 174 (accept_3_5 17 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 174 2 8 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 174 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 174 2 7 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 118 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 174 2 6 59 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 174 (accept_3_5 11 118 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 174 2 5 59 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 174
  (Polychromatic418967fa.accept_10_9_8_4_1_970 9 118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 174 2 4 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 174 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 118 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 174 2 3 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 174 (accept_3_5 5 118 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 174 2 2 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 174 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 118 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 174 2 1 59 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 174 (Polychromatic418967fa.accept_19_1_4_3_1_8404 1
  118 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  174))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 117 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 117 174 3 19 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 117 174 (Polychromatic418967fa.accept_12_8_9_6_1_127 56 117 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 55
  117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 117 174 3 18 39 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 117 174
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 174 (Polychromatic418967fa.accept_10_2_7_4_1_967 52 117 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 174 3 17 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 50
  117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 174
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 49 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 117 174 3 16 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 117 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 174 (Polychromatic418967fa.accept_7_4_5_6_1_344
  46 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 117 174 3 15 39 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 117 174
  (Polychromatic418967fa.accept_12_8_9_6_1_127 44 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 117 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 174 3 14 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 174 (Polychromatic418967fa.accept_10_1_7_4_1_968
  41 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 174
  (Polychromatic418967fa.accept_12_4_9_6_1_440 40 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 117 174 3 13 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 117 174 (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 117 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 174
  (Polychromatic418967fa.accept_21_16_12_6_1_8274 37 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 117 174 3 12 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 117 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 174
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 34 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 174 3 11 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 117 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 174 3 10 39 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 174
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 174 (Polychromatic418967fa.accept_12_4_9_6_1_440 28 117 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 174 3 9 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 174 (Polychromatic418967fa.accept_12_2_9_6_1_439
  26 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 117 174
  (Polychromatic418967fa.accept_7_4_5_6_1_344 25 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 117 174 3 8 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 117 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 117 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 174 3 7 39 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 174
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 117 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 174 3 6 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 174
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 117 174 (Polychromatic418967fa.accept_11_5_7_9_1_2696 16 117 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 174 3 5 39 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 174
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 174 (Polychromatic418967fa.accept_10_3_7_4_1_584 13 117 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 174 3 4 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 174
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 10 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 117 174 3 3 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 117 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 117 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 117 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 117 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 174 3 2 39 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 174
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 117 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 117 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 117 174 3 1 39 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 117 174 (Polychromatic418967fa.accept_10_2_7_4_1_967 2 117 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 174
  (Polychromatic418967fa.accept_7_1_5_6_1_59 1 117 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 117 174)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 116 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 116 174 58 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 57 116 174 (Polychromatic418967fa.accept_12_9_8_6_1_466 57 116 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 116 174 2 28 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 116 174 (accept_3_4 55 116 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 54 116 174 2 27 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 116 174 (Polychromatic418967fa.accept_13_1_12_5_1_1601 53 116
  174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 174 2 26 58 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 174
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 174 2 25 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 174 (accept_3_4 49 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 174 2 24 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 116 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 174 2 23 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 174
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 174 2 22 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 174 (accept_3_4 43 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 174 2 21 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 174 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 116 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 174 2 20 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 174
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 174 2 19 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 174 (accept_3_4 37 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 174 2 18 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 116 174 (Polychromatic418967fa.accept_10_5_6_4_1_64 35 116 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 174 2 17 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 116 174 2 16 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 116 174 (accept_3_4 31 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 116 174 2 15 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 29 116 174 29 1 4 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 116 174 2 14 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 116 174 (Polychromatic418967fa.accept_12_3_8_6_1_895 27 116 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 174 2 13 58 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 174 (accept_3_4 25 116 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 174 2 12 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 174
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 116 174 2 11 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 116 174 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 116 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 116 174 2 10 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 116 174 (accept_3_4 19 116 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 116 174 2 9 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 116 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 174 2 8 58 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 174
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 116 174 2 7 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 116 174 (accept_3_4 13 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  116 174 2 6 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 116 174 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 116 174 2 5 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 116 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 116 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 174 2 4 58 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 174 (accept_3_4 7 116 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 116 174 2 3 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 116 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 116 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 174 2 2 58 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 174
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 116 174 2 1 58 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 116 174 (accept_3_4 1 116 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  174))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 115 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 115 174 (accept_3_5 59 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 115 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 115 174 (accept_3_5 56 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 115 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 115 174
  (Polychromatic418967fa.accept_17_3_13_4_1_8530 54 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 115 174 (accept_3_5 53 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 115 174 (Polychromatic418967fa.accept_14_10_3_6_1_2728 52 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 115 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 115 174 (accept_3_5 50 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 174
  (Polychromatic418967fa.accept_15_3_10_9_1_769 48 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 115 174 (accept_3_5 47 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 115 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 115 174 (accept_3_5 44 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 115 174 (Polychromatic418967fa.accept_16_11_3_14_1_5043 43 115 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 174
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 115 174 (accept_3_5 41 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 115 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 115 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 174 (accept_3_5 38 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 174
  (Polychromatic418967fa.accept_10_6_5_4_1_571 36 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 115 174 (accept_3_5 35 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 115 174 (Polychromatic418967fa.accept_15_4_10_9_1_4298 34 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 174 (accept_3_5 32 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 115 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 174
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 115 174 (accept_3_5 29 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 115 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 115 174 (Polychromatic418967fa.accept_15_12_10_9_1_798 27 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 174 (accept_3_5 26 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 115 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 115 174
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 174 (accept_3_5 23 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 115 174 (accept_3_5 20 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 115 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 115 174
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 115 174 (accept_3_5 17 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 115 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 115 174 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 115 174 (accept_3_5 14 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 174
  (Polychromatic418967fa.accept_15_12_10_9_1_798 12 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 174 (accept_3_5 11 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 115 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 115 174 (accept_3_5 8 115 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 115 174 (Polychromatic418967fa.accept_11_7_5_9_1_884 7 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 174
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 115 174 (accept_3_5 5 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  115 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 115 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 115 174 (Polychromatic418967fa.accept_13_3_11_5_1_2348 3 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 174 (accept_3_5 2 115 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 115 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 115 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  174)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 114 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 114 174 6 10 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 114 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 114 174 2 29 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 114 174 3 19 38 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 174 2 28 57 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 114 174 6 9 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 114 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 114 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 114 174 2 26 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 114 174 3 17 38 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 174 2 25 57 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 174
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 174 6 8 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 114 174 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 114 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 114 174 2 23 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 114 174 3 15 38 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 174 2 22 57 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 174
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 174 6 7 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 114 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 114 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 114 174 2 20 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 114 174 3 13 38 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 174 2 19 57 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 114 174 6 6 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 114 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 114 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 114 174 2 17 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 114 174 3 11 38 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 174 2 16 57 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 174
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 174 6 5 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 114 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 114 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 114 174 2 14 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 114 174 3 9 38 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 114 174 2 13 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 114 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 114 174 6 4 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 114 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 114 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 114 174 2 11 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 114 174 3 7 38 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 114 174 2 10 57 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 114 174
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 174 6 3 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 114 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 114 174 2 8 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 114 174 3 5 38 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 114 174 2 7 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 114 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 13
  114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 174 6 2 19 29 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 114 174 2 5 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 114 174 3 3 38 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 114 174 2 4 57 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 114 174 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 114 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 174 6 1 19 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 114 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 174 2 2 57 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 174 3 1 38 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 174 2 1 57 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 174
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 114 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 174))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 113 174 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 113 174 (accept_3_4 61 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 113 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 113 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 113 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 174 (accept_3_4 58 113 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 174 (Polychromatic418967fa.accept_10_7_3_4_1_978
  57 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 174 (accept_3_4 55 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 174 (accept_3_4 52 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 174
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 174 (accept_3_4 49 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 174 (Polychromatic418967fa.accept_15_3_8_9_1_795 48 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 174 (accept_3_4 46 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 174 (Polychromatic418967fa.accept_16_13_1_14_1_2855 45 113 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 174
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 174 (accept_3_4 43 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 174 (Polychromatic418967fa.accept_13_2_9_5_1_959 41 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 174 (accept_3_4 40 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 113 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 174 (accept_3_4 37 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 174 (Polychromatic418967fa.accept_16_4_1_14_1_3908 36 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 174 (accept_3_4 34 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 174
  (Polychromatic418967fa.accept_15_2_8_9_1_4294 32 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 174 (accept_3_4 31 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 174 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 174 (accept_3_4 28 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 174 (accept_3_4 25 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 174 (accept_3_4 22 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 174 (Polychromatic418967fa.accept_14_7_1_6_1_3514 21 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 174 (accept_3_4 19 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 174 (Polychromatic418967fa.accept_15_3_8_9_1_795 18 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 174 (accept_3_4 16 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 174
  (Polychromatic418967fa.accept_13_1_9_5_1_1598 14 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 174 (accept_3_4 13 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 174 (accept_3_4 10 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 174
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 174 (accept_3_4 7 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 174 (accept_3_4 4 113 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 113 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 174
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 174 (accept_3_4 1 113 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  174)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 112 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 112 174 2 31 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 112 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 112 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 112 174 2 30 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 112 174 (accept_3_5 59 112 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 112 174 2 29 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 112 174 (Polychromatic418967fa.accept_10_7_2_4_1_569
  57 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 174 2 28 56 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 174
  (Polychromatic418967fa.accept_9_1_4_3_1_201 55 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 174 2 27 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 174 (accept_3_5 53 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 174 2 26 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 112 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 174 2 25 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 174
  (Polychromatic418967fa.accept_13_10_8_5_1_1616 49 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 174 2 24 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 112 174 (accept_3_5 47 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 112 174 2 23 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 112 174 (Polychromatic418967fa.accept_12_9_4_6_1_460 45 112 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 174 2 22 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 174
  (Polychromatic418967fa.accept_9_7_4_3_1_204 43 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 112 174 2 21 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 112 174 (accept_3_5 41 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 112 174 2 20 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 112 174 (Polychromatic418967fa.accept_12_3_4_6_1_434 39 112 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 112 174 2 19 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 112 174
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 112 174 2 18 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 112 174 (accept_3_5 35 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 112 174 2 17 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 112 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 112 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 112 174 2 16 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 112 174
  (Polychromatic418967fa.accept_15_1_7_9_1_20 31 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 112 174 2 15 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 112 174 (accept_3_5 29 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 112 174 2 14 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 112 174 (Polychromatic418967fa.accept_10_7_2_4_1_569 27 112 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 174 2 13 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 174
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 174 2 12 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 112 174 (accept_3_5 23 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 112 174 2 11 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 112 174 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 112 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 174 2 10 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 174
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 112 174 2 9 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 112 174 (accept_3_5 17 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  112 174 2 8 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 112 174 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 112 174 2 7 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 112 174 (Polychromatic418967fa.accept_15_13_7_9_1_3210 13 112 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 174 2 6 56 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 174 (accept_3_5 11 112 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 174 2 5 56 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 174
  (Polychromatic418967fa.accept_12_9_4_6_1_460 9 112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 112 174 2 4 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 112 174 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 112 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 112 174 2 3 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 112 174 (accept_3_5 5 112 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 112 174 2 2 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 112 174 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 112 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 112 174 2 1 56 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 112 174 (Polychromatic418967fa.accept_9_1_4_3_1_201 1
  112 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  174))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 111 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 111 174 3 21 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 111 174 (Polychromatic418967fa.accept_12_2_3_6_1_112 62 111 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 61
  111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 111 174 3 20 37 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 111 174
  (Polychromatic418967fa.accept_15_14_6_9_1_2274 59 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 111 174 (Polychromatic418967fa.accept_12_10_3_6_1_882 58 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 111 174 3 19 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 111 174 (Polychromatic418967fa.accept_12_8_3_6_1_909
  56 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 174
  (Polychromatic418967fa.accept_10_5_1_4_1_1444 55 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 174 3 18 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 111 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 174 (Polychromatic418967fa.accept_12_4_3_6_1_879
  52 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 111 174 3 17 37 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 111 174
  (Polychromatic418967fa.accept_12_2_3_6_1_112 50 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 49 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 174 3 16 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 174 (Polychromatic418967fa.accept_10_7_1_4_1_1447
  47 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 174
  (Polychromatic418967fa.accept_12_10_3_6_1_882 46 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 174 3 15 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 174 (Polychromatic418967fa.accept_12_8_3_6_1_909 44 111 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 174
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 43 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 111 174 3 14 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 111 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 174 (Polychromatic418967fa.accept_12_4_3_6_1_879
  40 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 174 3 13 37 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 174
  (Polychromatic418967fa.accept_12_2_3_6_1_112 38 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 174 3 12 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 174 (Polychromatic418967fa.accept_10_5_1_4_1_1444
  35 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 174
  (Polychromatic418967fa.accept_12_10_3_6_1_882 34 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 174 3 11 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 174 (Polychromatic418967fa.accept_11_10_1_9_1_2060 32 111 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 174
  (Polychromatic418967fa.accept_15_1_6_9_1_254 31 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 174 3 10 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 111 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 174 (Polychromatic418967fa.accept_12_4_3_6_1_879
  28 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 174 3 9 37 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 174
  (Polychromatic418967fa.accept_12_2_3_6_1_112 26 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 25 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 174 3 8 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 174
  (Polychromatic418967fa.accept_16_7_15_14_1_2889 23 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 111 174 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 111 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 174 3 7 37 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 174
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 174 (Polychromatic418967fa.accept_14_5_13_6_1_3574 19 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 174 3 6 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 174
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 174 3 5 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 174 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 111 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 174 3 4 37 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 174
  (Polychromatic418967fa.accept_13_11_7_5_1_2314 11 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 174 (Polychromatic418967fa.accept_11_10_1_9_1_2060 10 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 174 3 3 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 174 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 111 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 174
  (Polychromatic418967fa.accept_10_7_1_4_1_1447 7 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 174 3 2 37 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 174 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 111 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 174 3 1 37 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 174
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 111 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 111 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111 174))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 110 174 (Eq.refl Bool.true) (allA_succ_of_gcd 64 110 174 2 32 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 174
  (Polychromatic418967fa.accept_12_3_2_6_1_138 63 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 174 2 31 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 174 (accept_3_4 61 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 174 2 30 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 110 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 174 2 29 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 174
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 174 2 28 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 174 (accept_3_4 55 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 174 2 27 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 174 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 110 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 174 2 26 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 174
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 174 2 25 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 174 (accept_3_4 49 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 174 2 24 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 174 (Polychromatic418967fa.accept_17_13_8_4_1_2514 47 110 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 174 2 23 55 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 174
  (Polychromatic418967fa.accept_12_9_2_6_1_455 45 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 110 174 2 22 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 110 174 (accept_3_4 43 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 174 2 21 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 110 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 174 2 20 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 174
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 174 2 19 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 174 (accept_3_4 37 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 174 2 18 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 174 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 110 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 174 2 17 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 174
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 174 2 16 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 174 (accept_3_4 31 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 174 2 15 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 110 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 174 2 14 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 174
  (Polychromatic418967fa.accept_12_3_2_6_1_138 27 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 174 2 13 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 174 (accept_3_4 25 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 174 2 12 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 110 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 174 2 11 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 174
  (Polychromatic418967fa.accept_12_9_2_6_1_455 21 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 174 2 10 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 174 (accept_3_4 19 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 174 2 9 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 174 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 110 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 174 2 8 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 174 (Polychromatic418967fa.accept_7_1_5_6_1_59 15
  110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 174 2 7 55 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 174 (accept_3_4 13
  110 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 174 2 6 55 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 174
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 110 174 2 5 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 110 174 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 110 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 174 2 4 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 174 (accept_3_4 7 110 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 110 174 2 3 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 110 174 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 110 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 174 2 2 55 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 174 (Polychromatic418967fa.accept_12_3_2_6_1_138 3
  110 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 110 174 2 1 55 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 110 174 (accept_3_4 1
  110 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  174))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 109 174 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 109 174 (accept_3_5 65 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 174 (Polychromatic418967fa.accept_19_7_14_3_1_1793 64 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 174 (accept_3_5 62 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 174
  (Polychromatic418967fa.accept_9_6_1_3_1_191 60 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 174 (accept_3_5 59 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 174 (Polychromatic418967fa.accept_15_12_4_9_1_3204 57 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 174 (accept_3_5 56 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 109 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 174 (accept_3_5 53 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 52 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 174 (accept_3_5 50 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 174
  (Polychromatic418967fa.accept_10_8_9_4_1_961 48 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 174 (accept_3_5 47 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 174 (Polychromatic418967fa.accept_17_12_7_4_1_7231 46 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 174 (accept_3_5 44 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 174
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 174 (accept_3_5 41 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 174 (accept_3_5 38 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 174
  (Polychromatic418967fa.accept_15_6_4_9_1_1438 36 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 174 (accept_3_5 35 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 174 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 174 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 174 (accept_3_5 32 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 174
  (Polychromatic418967fa.accept_7_2_4_6_1_166 30 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 174 (accept_3_5 29 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 174 (Polychromatic418967fa.accept_10_8_9_4_1_961 28 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 174 (accept_3_5 26 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 174 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 174
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 174 (accept_3_5 23 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 174 (Polychromatic418967fa.accept_15_6_4_9_1_1438 21 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 174 (accept_3_5 20 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 109 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 174
  (Polychromatic418967fa.accept_10_8_9_4_1_961 18 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 174 (accept_3_5 17 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 174 (accept_3_5 14 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 174
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 174 (accept_3_5 11 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 174 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 174 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 174 (accept_3_5 8 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 174
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 174 (accept_3_5 5 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 174 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 109 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 174 (accept_3_5 2 109 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 174 (Polychromatic418967fa.accept_11_1_10_9_1_871 1 109 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  174)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 108 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 108 174 6 11 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 108 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 174 2 32 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 174 3 21 36 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 174 2 31 54 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 174
  (Polychromatic418967fa.accept_13_9_4_5_1_1651 61 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 174 6 10 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 174 (Polychromatic418967fa.accept_10_9_8_4_1_970 59 108 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 174 2 29 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 174 3 19 36 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 174 2 28 54 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 174
  (Polychromatic418967fa.accept_15_10_3_9_1_3285 55 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 174 6 9 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 174 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 108 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 174 2 26 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 174 3 17 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 174 2 25 54 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 174
  (Polychromatic418967fa.accept_10_9_8_4_1_970 49 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 174 6 8 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 108 174 (Polychromatic418967fa.accept_19_9_13_3_1_9829 47 108 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 174 2 23 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 174 3 15 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 174 2 22 54 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 174
  (Polychromatic418967fa.accept_15_13_3_9_1_1482 43 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 174 6 7 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 108 174 (Polychromatic418967fa.accept_13_2_4_5_1_3152 41 108 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 174 2 20 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 174 3 13 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 174 2 19 54 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 174
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 174 6 6 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 108 174 (Polychromatic418967fa.accept_13_9_4_5_1_1651 35 108 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 174 2 17 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 174 3 11 36 58 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 174 2 16 54 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 174
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 31 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 174 6 5 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 174 (Polychromatic418967fa.accept_10_9_8_4_1_970 29 108 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 174 2 14 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 174 3 9 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 174 2 13 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 174
  (Polychromatic418967fa.accept_7_4_3_6_1_340 25 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 174 6 4 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 174 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 108 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 174 2 11 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 174 3 7 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 174 2 10 54 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 174
  (Polychromatic418967fa.accept_10_9_8_4_1_970 19 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 174 6 3 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 174 (Polychromatic418967fa.accept_14_3_10_6_1_1136 17 108 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 108 174 2 8 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 108 174 3 5 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 108 174 2 7 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 108 174 (Polychromatic418967fa.accept_15_13_3_9_1_1482
  13 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 174 6 2 18 29
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 174
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 108 174 2 5 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 108 174 3 3 36 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 108 174 2 4 54 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 108 174 (Polychromatic418967fa.accept_19_7_13_3_1_4171 7 108 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 174 6 1 18 29 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 174 (Polychromatic418967fa.accept_15_5_3_9_1_283 5 108 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 108 174 2 2 54 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 108 174 3 1 36 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 108 174 2 1 54 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 108 174
  (Polychromatic418967fa.accept_13_1_4_5_1_113 1 108 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 174))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 107 174 (Eq.refl
  Bool.true) (allA_succ_of_accept 67 107 174 (accept_3_4 67 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 107 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 107 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 107 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 174 (accept_3_4 64 107 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 174 (Polychromatic418967fa.accept_10_3_7_4_1_584
  63 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 174
  (Polychromatic418967fa.accept_10_2_7_4_1_967 62 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 174 (accept_3_4 61 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 174 (accept_3_4 58 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 174 (accept_3_4 55 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 174 (Polychromatic418967fa.accept_11_10_8_9_1_492 54 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 174 (accept_3_4 52 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 174
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 174 (accept_3_4 49 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 174 (Polychromatic418967fa.accept_13_9_3_5_1_1605 48 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 174 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 174 (accept_3_4 46 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 174
  (Polychromatic418967fa.accept_23_21_15_13_1_9828 44 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 107 174 (accept_3_4 43 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 107 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 107 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 107 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 174 (accept_3_4 40 107 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 174 (Polychromatic418967fa.accept_7_4_2_6_1_337
  39 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 174
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 174 (accept_3_4 37 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 174 (Polychromatic418967fa.accept_13_9_3_5_1_1605 35 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 174 (accept_3_4 34 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 107 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 174
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 174 (accept_3_4 31 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 174 (Polychromatic418967fa.accept_19_11_12_3_1_8407 30 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 174 (accept_3_4 28 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 174 (Polychromatic418967fa.accept_13_1_3_5_1_140 27 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 174
  (Polychromatic418967fa.accept_15_11_2_9_1_1480 26 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 174 (accept_3_4 25 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 174 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 174 (accept_3_4 22 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 174 (accept_3_4 19 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 174 (accept_3_4 16 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 174 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 174
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 174 (accept_3_4 13 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 174 (Polychromatic418967fa.accept_10_2_7_4_1_967 12 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 174 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 174 (accept_3_4 10 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 174
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 174 (accept_3_4 7 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 174 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 174 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 174 (accept_3_4 4 107 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 174 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 107 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 174
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 174 (accept_3_4 1 107 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  174)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 106 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 106 174 2 34 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 106 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 106 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 106 174 2 33 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 106 174 (accept_3_5 65 106 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 106 174 2 32 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 106 174 (Polychromatic418967fa.accept_12_3_10_6_1_442
  63 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 174 2 31 53 87
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 61 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 174 2 30 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 174 (accept_3_5 59 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 174 2 29 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 174 (Polychromatic418967fa.accept_11_2_7_9_1_890 57 106 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 174 2 28 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 174
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 174 2 27 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 174 (accept_3_5 53 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 174 2 26 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 174 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 106 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 174 2 25 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 174
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 174 2 24 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 174 (accept_3_5 47 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 174 2 23 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 174 (Polychromatic418967fa.accept_10_5_6_4_1_64 45 106 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 174 2 22 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 174
  (Polychromatic418967fa.accept_13_4_2_5_1_4045 43 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 106 174 2 21 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 106 174 (accept_3_5 41 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 174 2 20 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 174 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 106 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 174 2 19 53 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 174
  (Polychromatic418967fa.accept_7_2_1_6_1_173 37 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 174 2 18 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 174 (accept_3_5 35 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 174 2 17 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 174 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 106 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 174 2 16 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 174
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 174 2 15 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 174 (accept_3_5 29 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 174 2 14 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 174 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 106 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 174 2 13 53 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 174
  (Polychromatic418967fa.accept_10_5_6_4_1_64 25 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 174 2 12 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 174 (accept_3_5 23 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 174 2 11 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 174 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 106 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 174 2 10 53 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 174
  (Polychromatic418967fa.accept_7_5_1_6_1_163 19 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 174 2 9 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 174 (accept_3_5 17 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 174 2 8 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 174 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 174 2 7 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 174 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 106 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 174 2 6 53 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 174 (accept_3_5 11 106 174
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 174 2 5 53 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 174
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 174 2 4 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 174 (Polychromatic418967fa.accept_13_7_2_5_1_2344 7 106 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 174 2 3 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 174 (accept_3_5 5 106 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 174 2 2 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 174 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 106 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 174 2 1 53 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 174 (Polychromatic418967fa.accept_9_1_7_3_1_41 1
  106 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  174))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 105 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 105 174 3 23 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 105 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 105 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 67
  105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 105 174 3 22 35 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 105 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 105 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 64 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 174 3 21 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 62
  105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 105 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 61 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 105 174 3 20 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 105 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 105 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 174 (Polychromatic418967fa.accept_9_4_6_3_1_179
  58 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 105 174 3 19 35 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 105 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 56 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 105 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 55 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 105 174 3 18 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 53
  105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 105 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 52 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 105 174 3 17 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 105 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 105 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 174 (Polychromatic418967fa.accept_9_4_6_3_1_179
  49 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 105 174 3 16 35 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 105 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 105 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 46 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 174 3 15 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 44
  105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 43 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 105 174 3 14 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 105 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 105 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 174 (Polychromatic418967fa.accept_9_4_6_3_1_179
  40 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 105 174 3 13 35 58
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 105 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 105 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 174 3 12 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 105 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 35
  105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 105 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 174 3 11 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 105 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 31
  105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 105 174 3 10 35 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 105 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 105 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 174 3 9 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 26
  105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 105 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 105 174 3 8 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 105 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 105 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 174 3 7 35 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 105 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 105 174 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 174 3 6 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 174
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 105 174 3 5 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 105 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 105 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 174 3 4 35 58 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 105 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 174 3 3 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 174 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 105 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 105 174
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 105 174 3 2 35 58 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 105 174 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 174 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 105 174
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 174 3 1 35 58 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 174
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 105 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 174 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 105 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105
  174)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 104 174 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 104 174 2 35 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 104 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 104 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 174 2 34 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 174 (accept_3_4 67 104 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 174 2 33 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 104 174 (Polychromatic418967fa.accept_9_2_5_3_1_37 65
  104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 104 174 2 32 52 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 104 174
  (Polychromatic418967fa.accept_12_3_8_6_1_895 63 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 104 174 2 31 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 104 174 (accept_3_4 61 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 104 174 2 30 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 104 174 (Polychromatic418967fa.accept_20_19_4_14_1_8345 59 104 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 174 2 29 52 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 174
  (Polychromatic418967fa.accept_12_9_8_6_1_466 57 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 174 2 28 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 104 174 (accept_3_4 55 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 104 174 2 27 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 104 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 104 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 174 2 26 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 174
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 104 174 2 25 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 104 174 (accept_3_4 49 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 104 174 2 24 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 104 174 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 104 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 104 174 2 23 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 104 174
  (Polychromatic418967fa.accept_12_9_8_6_1_466 45 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 104 174 2 22 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 104 174 (accept_3_4 43 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 104 174 2 21 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 104 174 (Polychromatic418967fa.accept_23_18_12_13_1_9827 41 104 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 104 174 2 20 52 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 104 174
  (Polychromatic418967fa.accept_12_3_8_6_1_895 39 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 104 174 2 19 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 104 174 (accept_3_4 37 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 104 174 2 18 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 104 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 104 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 104 174 2 17 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 104 174
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 104 174 2 16 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 104 174 (accept_3_4 31 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 104 174 2 15 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 104 174 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 104 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 174 2 14 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 174
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 174 2 13 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 174 (accept_3_4 25 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 174 2 12 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 104 174 (Polychromatic418967fa.accept_15_8_14_9_1_4216 23 104 174 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 174 2 11 52 87 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 174
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 104 174 2 10 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 104 174 (accept_3_4 19 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 174 2 9 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 174 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 104 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 174 2 8 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 174 (Polychromatic418967fa.accept_9_6_5_3_1_205 15
  104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 174 2 7 52 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 174 (accept_3_4 13
  104 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 174 2 6 52 87 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 174
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 174 2 5 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 174 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 104 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 174 2 4 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 174 (accept_3_4 7 104 174 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 174 2 3 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 174 (Polychromatic418967fa.accept_15_5_14_9_1_274 5 104 174 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 174 2 2 52 87 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 174 (Polychromatic418967fa.accept_12_3_8_6_1_895 3
  104 174 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 104 174 2 1 52 87 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 104 174 (accept_3_4 1
  104 174 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  174)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_174_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


