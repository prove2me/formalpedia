-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch201
-- name    : Polychromatic418967fa_Branch201
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:21:51.115974+00:00
-- url     : https://prove2.me/theorems/c9f3058e-dac7-4d75-9db0-23b825b092cc
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch201_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_201 : allB 201 201 :=
  allB_succ' 2 200 201 (Eq.refl Bool.true) (allA_succ_of_accept 1 200 201 (accept_3_4 1 200 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 200 201)) (allB_succ' 3 199 201 (Eq.refl Bool.true) (allA_succ_of_accept 2 199 201
  (accept_3_5 2 199 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 201
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 199 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 199 201))) (allB_succ' 4 198 201 (Eq.refl Bool.true) (allA_succ_of_gcd 3 198 201 3 1 66 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 198 201
  (Polychromatic418967fa.accept_12_2_6_9_1_19 2 198 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 198 201 (Polychromatic418967fa.accept_13_1_3_6_1_158 1 198 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 198 201)))) (allB_succ' 5 197 201 (Eq.refl Bool.true) (allA_succ_of_accept 4
  197 201 (accept_3_4 4 197 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 197 201
  (Polychromatic418967fa.accept_7_3_1_5_1_44 3 197 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 197 201 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 197 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 201 (accept_3_4 1 197 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 197 201))))) (allB_succ' 6 196 201 (Eq.refl Bool.true) (allA_succ_of_accept 5 196 201
  (accept_3_5 5 196 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 196 201
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 196 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 196 201 (Polychromatic418967fa.accept_13_3_1_6_1_509 3 196 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 196 201 (accept_3_5 2 196 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 196 201 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 196 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 196 201)))))) (allB_succ' 7 195 201 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 195 201 3 2 65 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 195 201 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 195 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 201 (Polychromatic418967fa.accept_7_4_6_5_1_141 4 195 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 195 201 3 1 65 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 195 201
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 195 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 201 (Polychromatic418967fa.accept_7_1_6_5_1_39 1 195 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 195 201))))))) (allB_succ' 8 194 201 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 201 (accept_3_4 7 194 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  194 201 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 194 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 194 201 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 194 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 194 201 (accept_3_4 4 194 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 194 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 194 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 194 201
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 194 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 194 201 (accept_3_4 1 194 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  201)))))))) (allB_succ' 9 193 201 (Eq.refl Bool.true) (allA_succ_of_accept 8 193 201 (accept_3_5 8 193 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 193 201 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 193 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 193 201
  (Polychromatic418967fa.accept_7_6_4_5_1_314 6 193 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 193 201 (accept_3_5 5 193 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  193 201 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 193 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 193 201 (Polychromatic418967fa.accept_12_3_1_9_1_202 3 193 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 193 201 (accept_3_5 2 193 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 201 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 193 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 193 201))))))))) (allB_succ' 10 192 201 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 192 201 3 3 64 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 192 201 (Polychromatic418967fa.accept_7_1_3_5_1_33 8 192 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 192 201 (Polychromatic418967fa.accept_15_7_12_6_1_1327
  7 192 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 201 3 2 64 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 201
  (Polychromatic418967fa.accept_13_5_10_6_1_2361 5 192 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 192 201 (Polychromatic418967fa.accept_13_4_10_6_1_989 4 192 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 192 201 3 1 64 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 192 201 (Polychromatic418967fa.accept_7_2_3_5_1_34 2 192 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 192 201
  (Polychromatic418967fa.accept_7_1_3_5_1_33 1 192 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 192 201)))))))))) (allB_succ' 11 191 201 (Eq.refl Bool.true) (allA_succ_of_accept 10 191 201 (accept_3_4 10
  191 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 201
  (Polychromatic418967fa.accept_15_9_11_6_1_637 9 191 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 191 201 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 191 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 191 201 (accept_3_4 7 191 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 191 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 191 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 191 201 (Polychromatic418967fa.accept_9_5_2_3_1_194 5
  191 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 201 (accept_3_4 4 191
  201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 201
  (Polychromatic418967fa.accept_7_3_2_5_1_147 3 191 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 191 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 191 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 201 (accept_3_4 1 191 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 191 201))))))))))) (allB_succ' 12 190 201 (Eq.refl Bool.true) (allA_succ_of_accept 11 190 201
  (accept_3_5 11 190 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 190 201
  (Polychromatic418967fa.accept_7_3_1_5_1_44 10 190 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 190 201 (Polychromatic418967fa.accept_20_9_10_1_1_192 9 190 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 190 201 (accept_3_5 8 190 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 190 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 190 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 190 201 (Polychromatic418967fa.accept_7_6_1_5_1_322 6
  190 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 190 201 (accept_3_5 5 190
  201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 190 201
  (Polychromatic418967fa.accept_7_4_1_5_1_540 4 190 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 190 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 190 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 201 (accept_3_5 2 190 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 190 201 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 190 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 201)))))))))))) (allB_succ' 13 189 201 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 189 201 3 4 63 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 189 201 (Polychromatic418967fa.accept_15_11_9_6_1_1321 11 189 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 201 (Polychromatic418967fa.accept_19_10_18_11_1_10502 10
  189 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 201 3 3 63 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 201
  (Polychromatic418967fa.accept_10_8_9_1_1_189 8 189 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 189 201 (Polychromatic418967fa.accept_16_7_13_9_1_1653 7 189 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 189 201 3 2 63 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 189 201 (Polychromatic418967fa.accept_10_5_9_1_1_187 5 189 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 201
  (Polychromatic418967fa.accept_8_4_5_1_1_299 4 189 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 189 201 3 1 63 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 189 201 (Polychromatic418967fa.accept_10_2_9_1_1_185 2 189 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 201 (Polychromatic418967fa.accept_11_1_2_3_1_688 1 189 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 189 201))))))))))))) (allB_succ' 14 188 201
  (Eq.refl Bool.true) (allA_succ_of_accept 13 188 201 (accept_3_4 13 188 201 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 188 201 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 188 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 188 201 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 188 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 188 201 (accept_3_4 10 188 201
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 188 201 (Polychromatic418967fa.accept_10_9_8_1_1_1331
  9 188 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 188 201
  (Polychromatic418967fa.accept_7_1_6_5_1_39 8 188 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 188 201 (accept_3_4 7 188 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  188 201 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 188 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 188 201 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 188 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 201 (accept_3_4 4 188 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 201 (Polychromatic418967fa.accept_10_3_8_1_1_182 3 188 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 201
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 188 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 201 (accept_3_4 1 188 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  201)))))))))))))) (allB_succ' 15 187 201 (Eq.refl Bool.true) (allA_succ_of_accept 14 187 201 (accept_3_5 14 187 201
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 201 (Polychromatic418967fa.accept_9_4_7_3_1_43 13
  187 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 201
  (Polychromatic418967fa.accept_13_12_5_6_1_1050 12 187 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 201 (accept_3_5 11 187 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 187 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 201 (Polychromatic418967fa.accept_18_9_7_3_1_3871 9 187 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 201 (accept_3_5 8 187 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 201 (Polychromatic418967fa.accept_21_7_19_12_1_5579 7 187 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 201
  (Polychromatic418967fa.accept_4_2_3_1_1_2 6 187 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 201 (accept_3_5 5 187 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 201 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 187 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 201 (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 187 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 201 (accept_3_5 2 187 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 201 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 187 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 201))))))))))))))) (allB_succ' 16 186 201 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 186 201 3 5 62 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 186 201 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 186 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 186 201 (Polychromatic418967fa.accept_7_6_4_5_1_314
  13 186 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 186 201 3 4 62 67
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 186 201
  (Polychromatic418967fa.accept_4_3_2_1_1_50 11 186 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 186 201 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 186 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 186 201 3 3 62 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 186 201 (Polychromatic418967fa.accept_7_1_4_5_1_35 8 186 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 201
  (Polychromatic418967fa.accept_4_3_2_1_1_50 7 186 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 186 201 3 2 62 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 186 201 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 186 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 186 201 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 186 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 186 201 3 1 62 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 186 201
  (Polychromatic418967fa.accept_7_2_4_5_1_313 2 186 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 186 201 (Polychromatic418967fa.accept_7_1_4_5_1_35 1 186 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 186 201)))))))))))))))) (allB_succ' 17 185 201 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 185 201 (accept_3_4 16 185 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 185 201 (Polychromatic418967fa.accept_7_1_3_5_1_33 15 185 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 185 201 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 185 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 201 (accept_3_4 13 185 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 201 (Polychromatic418967fa.accept_14_12_3_5_1_1868 12 185 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 185 201
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 185 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 185 201 (accept_3_4 10 185 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  185 201 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 185 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 185 201 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 185 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 201 (accept_3_4 7 185 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 185 201 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 185 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 185 201
  (Polychromatic418967fa.accept_13_5_3_6_1_3278 5 185 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 185 201 (accept_3_4 4 185 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  185 201 (Polychromatic418967fa.accept_12_3_5_9_1_176 3 185 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 185 201 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 185 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 201 (accept_3_4 1 185 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 185 201))))))))))))))))) (allB_succ' 18 184 201 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 184 201 (accept_3_5 17 184 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 184 201 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 184 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 184 201 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 184 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 184 201 (accept_3_5 14 184 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 184 201 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 184 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 184 201
  (Polychromatic418967fa.accept_13_12_2_6_1_2396 12 184 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 184 201 (accept_3_5 11 184 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 184 201 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 184 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 184 201 (Polychromatic418967fa.accept_13_9_2_6_1_514 9 184 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 184 201 (accept_3_5 8 184 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 184 201 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 184 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 184 201
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 184 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 184 201 (accept_3_5 5 184 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  184 201 (Polychromatic418967fa.accept_7_4_2_5_1_527 4 184 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 184 201 (Polychromatic418967fa.accept_7_3_2_5_1_147 3 184 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 184 201 (accept_3_5 2 184 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 184 201 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 184 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 201)))))))))))))))))) (allB_succ' 19 183 201
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 183 201 3 6 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 183 201 (Polychromatic418967fa.accept_7_3_1_5_1_44 17 183 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 201
  (Polychromatic418967fa.accept_13_3_1_6_1_509 16 183 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 183 201 3 5 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 183 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 183 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 201 (Polychromatic418967fa.accept_7_6_1_5_1_322 13 183 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 201 3 4 61 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 201
  (Polychromatic418967fa.accept_7_4_1_5_1_540 11 183 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 10 183 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 201 3 3 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 201 (Polychromatic418967fa.accept_10_8_3_1_1_1316 8 183 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 201
  (Polychromatic418967fa.accept_12_7_3_9_1_999 7 183 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 183 201 3 2 61 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 183 201 (Polychromatic418967fa.accept_12_5_3_9_1_541 5 183 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 201 (Polychromatic418967fa.accept_7_4_1_5_1_540 4 183 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 201 3 1 61 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 201
  (Polychromatic418967fa.accept_4_2_3_1_1_2 2 183 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 201 (Polychromatic418967fa.accept_12_1_3_9_1_174 1 183 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183 201))))))))))))))))))) (allB_succ' 20 182 201 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 182 201 (accept_3_4 19 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 182 201 (Polychromatic418967fa.accept_12_6_2_9_1_537 18 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 182 201 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 182 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 182 201 (accept_3_4 16 182 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 182 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 182 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 182 201
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 182 201 (accept_3_4 13 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 182 201 (Polychromatic418967fa.accept_15_12_2_6_1_2127 12 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 182 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 11 182 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 201 (accept_3_4 10 182 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 201 (Polychromatic418967fa.accept_10_9_2_1_1_840 9 182 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 182 201
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 182 201 (accept_3_4 7 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  182 201 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 182 201 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 182 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 201 (accept_3_4 4 182 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 182 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 182 201
  (Polychromatic418967fa.accept_16_2_6_9_1_3473 2 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 182 201 (accept_3_4 1 182 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  201)))))))))))))))))))) (allB_succ' 21 181 201 (Eq.refl Bool.true) (allA_succ_of_accept 20 181 201 (accept_3_5 20 181
  201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 201
  (Polychromatic418967fa.accept_11_8_5_3_1_694 19 181 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 181 201 (Polychromatic418967fa.accept_7_4_6_5_1_141 18 181 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 181 201 (accept_3_5 17 181 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 181 201 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 181 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 181 201 (Polychromatic418967fa.accept_7_1_6_5_1_39 15
  181 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 201 (accept_3_5 14
  181 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 201
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 181 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 181 201 (Polychromatic418967fa.accept_8_4_5_1_1_299 12 181 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 201 (accept_3_5 11 181 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 181 201 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 181 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 201 (Polychromatic418967fa.accept_15_9_1_6_1_657 9
  181 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 201 (accept_3_5 8 181
  201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 201
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 181 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 181 201 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 181 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 201 (accept_3_5 5 181 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 181 201 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 181 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 201 (Polychromatic418967fa.accept_12_3_1_9_1_202 3
  181 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 201 (accept_3_5 2 181
  201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 201 (Polychromatic418967fa.accept_7_1_6_5_1_39
  1 181 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 201)))))))))))))))))))))
  (allB_succ' 22 180 201 (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 201 3 7 60 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 180 201
  (Polychromatic418967fa.accept_19_1_9_11_1_438 20 180 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 180 201 (Polychromatic418967fa.accept_22_19_4_3_1_11760 19 180 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 180 201 3 6 60 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 180 201
  (Polychromatic418967fa.accept_13_4_11_6_1_1033 17 180 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 180 201 (Polychromatic418967fa.accept_27_16_18_12_1_11759 16 180 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 180 201 3 5 60 67 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 180 201
  (Polychromatic418967fa.accept_16_14_4_9_1_1646 14 180 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 180 201 (Polychromatic418967fa.accept_8_5_4_1_1_111 13 180 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 201 3 4 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 201 (Polychromatic418967fa.accept_16_11_4_9_1_851
  11 180 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 180 201
  (Polychromatic418967fa.accept_14_10_12_5_1_3466 10 180 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 180 201 3 3 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 180 201 (Polychromatic418967fa.accept_13_8_11_6_1_1035 8 180 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 180 201 (Polychromatic418967fa.accept_11_7_4_3_1_302 7
  180 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 201 3 2 60 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 180 201
  (Polychromatic418967fa.accept_8_5_4_1_1_111 5 180 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 180 201 (Polychromatic418967fa.accept_13_4_11_6_1_1033 4 180 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 180 201 3 1 60 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 180 201 (Polychromatic418967fa.accept_19_2_9_11_1_7515 2 180 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 180 201
  (Polychromatic418967fa.accept_17_1_10_14_1_1173 1 180 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 180 201)))))))))))))))))))))) (allB_succ' 23 179 201 (Eq.refl Bool.true) (allA_succ_of_accept 22 179 201
  (accept_3_4 22 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 201
  (Polychromatic418967fa.accept_17_4_9_14_1_5406 21 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 179 201 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 179 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 201 (accept_3_4 19 179 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 179 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 179 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 201 (Polychromatic418967fa.accept_13_4_10_6_1_989
  17 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 201 (accept_3_4 16
  179 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 201
  (Polychromatic418967fa.accept_7_1_4_5_1_35 15 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 179 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 14 179 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 201 (accept_3_4 13 179 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 179 201 (Polychromatic418967fa.accept_10_2_9_1_1_185 12 179 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 201
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 201 (accept_3_4 10 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 201 (Polychromatic418967fa.accept_7_2_4_5_1_313 9 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 201 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 201 (accept_3_4 7 179 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 179 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 201
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 201 (accept_3_4 4 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 201 (Polychromatic418967fa.accept_12_3_11_9_1_193 3 179 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 2 179 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 201 (accept_3_4 1 179 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 201))))))))))))))))))))))) (allB_succ' 24 178 201 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 178 201 (accept_3_5 23 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 178 201 (Polychromatic418967fa.accept_7_1_3_5_1_33 22 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 178 201 (Polychromatic418967fa.accept_22_21_2_3_1_6962 21 178 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 178 201 (accept_3_5 20 178 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 178 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 19 178 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 178 201
  (Polychromatic418967fa.accept_12_6_10_9_1_531 18 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 178 201 (accept_3_5 17 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 178 201 (Polychromatic418967fa.accept_7_2_3_5_1_34 16 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 178 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 15 178 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 201 (accept_3_5 14 178 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 178 201 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 178 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 201
  (Polychromatic418967fa.accept_11_1_2_3_1_688 12 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 178 201 (accept_3_5 11 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 178 201 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 178 201 (Polychromatic418967fa.accept_7_2_3_5_1_34 9 178 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 201 (accept_3_5 8 178 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 178 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 7 178 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 201
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 178 201 (accept_3_5 5 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  178 201 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 178 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 178 201 (Polychromatic418967fa.accept_4_3_2_1_1_50 3 178 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 201 (accept_3_5 2 178 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 201 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 178 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 201)))))))))))))))))))))))) (allB_succ' 25 177 201
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 177 201 3 8 59 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 177 201 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 177 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 201
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 177 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 177 201 3 7 59 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 177 201 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 177 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 201 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 177 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 201 3 6 59 67 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 201
  (Polychromatic418967fa.accept_7_3_2_5_1_147 17 177 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 201 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 177 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 201 3 5 59 67 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 201 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  177 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 201
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 177 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 177 201 3 4 59 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 177 201 (Polychromatic418967fa.accept_7_4_2_5_1_527 11 177 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 201 (Polychromatic418967fa.accept_7_3_2_5_1_147 10 177 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 201 3 3 59 67 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 201
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 177 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 201 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 177 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 201 3 2 59 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 201 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 177 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 201
  (Polychromatic418967fa.accept_7_4_2_5_1_527 4 177 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 177 201 3 1 59 67 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 177 201 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 177 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 201 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 177 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 201))))))))))))))))))))))))) (allB_succ' 26
  176 201 (Eq.refl Bool.true) (allA_succ_of_accept 25 176 201 (accept_3_4 25 176 201 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 176 201 (Polychromatic418967fa.accept_7_3_1_5_1_44 24 176 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 176 201 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  176 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 176 201 (accept_3_4 22
  176 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 176 201
  (Polychromatic418967fa.accept_23_21_15_17_1_10022 21 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 176 201 (Polychromatic418967fa.accept_7_6_1_5_1_322 20 176 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 176 201 (accept_3_4 19 176 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 176 201 (Polychromatic418967fa.accept_7_4_1_5_1_540 18 176 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 176 201
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 176 201 (accept_3_4 16 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 176 201 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 176 201 (Polychromatic418967fa.accept_13_1_7_6_1_142 14 176 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 176 201 (accept_3_4 13 176 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 176 201 (Polychromatic418967fa.accept_10_2_6_1_1_1296 12 176
  201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 176 201
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 176 201 (accept_3_4 10 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  176 201 (Polychromatic418967fa.accept_13_9_7_6_1_1673 9 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 176 201 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 176 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 176 201 (accept_3_4 7 176 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 176 201 (Polychromatic418967fa.accept_7_6_1_5_1_322 6 176 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 176 201
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 176 201 (accept_3_4 4 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  176 201 (Polychromatic418967fa.accept_7_3_1_5_1_44 3 176 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 176 201 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 176 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 176 201 (accept_3_4 1 176 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176 201)))))))))))))))))))))))))) (allB_succ' 27 175 201 (Eq.refl Bool.true)
  (allA_succ_of_accept 26 175 201 (accept_3_5 26 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 175 201 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 175 201 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 175 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 201 (accept_3_5 23 175 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 22 175 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 175 201
  (Polychromatic418967fa.accept_19_2_4_11_1_7507 21 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 175 201 (accept_3_5 20 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 175 201 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 175 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 18 175 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 201 (accept_3_5 17 175 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 201 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 175 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 201
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 201 (accept_3_5 14 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 201 (Polychromatic418967fa.accept_33_13_10_3_1_11758 13 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 201 (Polychromatic418967fa.accept_14_12_7_5_1_1107 12 175 201
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 201 (accept_3_5 11 175 201
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 10
  175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 201
  (Polychromatic418967fa.accept_10_9_5_1_1_1325 9 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 201 (accept_3_5 8 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 201 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 201 (Polychromatic418967fa.accept_4_2_3_1_1_2 6 175 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 201 (accept_3_5 5 175 201 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 201 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 201 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 201
  (Polychromatic418967fa.accept_12_3_7_9_1_1009 3 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 201 (accept_3_5 2 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 201 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 175 201 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 201)))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_201_segment_001))))))))))))))))))))))))))


