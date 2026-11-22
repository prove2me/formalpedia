-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch195
-- name    : Polychromatic418967fa_Branch195
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:22:37.471187+00:00
-- url     : https://prove2.me/theorems/04d18be7-281f-4208-bf84-8dedf5c3b60d
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch195_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_195 : allB 195 195 :=
  allB_succ' 2 194 195 (Eq.refl Bool.true) (allA_succ_of_accept 1 194 195 (accept_3_4 1 194 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 194 195)) (allB_succ' 3 193 195 (Eq.refl Bool.true) (allA_succ_of_accept 2 193 195
  (accept_3_5 2 193 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 193 195
  (Polychromatic418967fa.accept_9_1_4_6_1_5 1 193 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 193 195))) (allB_succ' 4 192 195 (Eq.refl Bool.true) (allA_succ_of_gcd 3 192 195 3 1 64 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 192 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 192 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 192 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 192 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 195)))) (allB_succ' 5 191 195 (Eq.refl Bool.true) (allA_succ_of_accept 4
  191 195 (accept_3_4 4 191 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 191 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 191 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 191 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 191 195 (accept_3_4 1 191 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 191 195))))) (allB_succ' 6 190 195 (Eq.refl Bool.true) (allA_succ_of_gcd 5 190 195 5 1 38 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 190 195
  (Polychromatic418967fa.accept_9_4_1_6_1_284 4 190 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 190 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 190 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 190 195 (accept_3_5 2 190 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 190 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 190 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 190 195)))))) (allB_succ' 7 189 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 189 195 3 2 63 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 189 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 189 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 4 189 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 195 3 1 63 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 189 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 189 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 195))))))) (allB_succ' 8 188 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 195 (accept_3_4 7 188 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  188 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 188 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 188 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 188 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 188 195 (accept_3_4 4 188 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 188 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 188 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 188 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 188 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 188 195 (accept_3_4 1 188 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  195)))))))) (allB_succ' 9 187 195 (Eq.refl Bool.true) (allA_succ_of_accept 8 187 195 (accept_3_5 8 187 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 195 (Polychromatic418967fa.accept_16_7_11_3_1_1330 7 187
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 195
  (Polychromatic418967fa.accept_14_6_5_13_1_367 6 187 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 195 (accept_3_5 5 187 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 187 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 187 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 195 (accept_3_5 2 187 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 187 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 195))))))))) (allB_succ' 10 186 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 186 195 3 3 62 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 186 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 186 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 186 195 (Polychromatic418967fa.accept_16_7_10_3_1_2210
  7 186 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 195 3 2 62 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 186 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 186 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 186 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 186 195 3 1 62 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 186 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 186 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 186 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 186 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 186 195)))))))))) (allB_succ' 11 185 195 (Eq.refl Bool.true) (allA_succ_of_gcd 10 185 195 5 2 37 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 185 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 185 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 185 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 185 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 185 195 (accept_3_4 7 185 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 185 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 185 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 185 195 5 1 37 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 185 195 (accept_3_4 4 185 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 185 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 185 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 195 (accept_3_4 1 185 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  195))))))))))) (allB_succ' 12 184 195 (Eq.refl Bool.true) (allA_succ_of_accept 11 184 195 (accept_3_5 11 184 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 184 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 10
  184 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 184 195
  (Polychromatic418967fa.accept_10_9_4_5_1_616 9 184 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 184 195 (accept_3_5 8 184 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  184 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 184 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 184 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 184 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 184 195 (accept_3_5 5 184 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 184 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 184 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 184 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 184 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 184 195 (accept_3_5 2 184 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  184 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 184 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 184 195)))))))))))) (allB_succ' 13 183 195 (Eq.refl Bool.true) (allA_succ_of_gcd 12 183 195 3 4
  61 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 183 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 183 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 195 3 3 61 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 183 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 183 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 183 195 3 2 61 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 183 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 183 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 183 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 195 3 1 61 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 183 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 183 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183 195))))))))))))) (allB_succ' 14 182 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 13 182 195 13 1 14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 12 182 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 182 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 182 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  182 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 182 195 (accept_3_4 10
  182 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 182 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 182 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 182 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 182 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 182 195 (accept_3_4 7 182 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 182 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 182 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 182 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  182 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 182 195 (accept_3_4 4 182
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 182 195
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 182 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 182 195 (Polychromatic418967fa.accept_16_2_6_3_1_5396 2 182 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 182 195 (accept_3_4 1 182 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 182 195)))))))))))))) (allB_succ' 15 181 195 (Eq.refl Bool.true) (allA_succ_of_accept 14 181 195
  (accept_3_5 14 181 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 195
  (Polychromatic418967fa.accept_9_4_1_6_1_284 13 181 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 181 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 181 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 181 195 (accept_3_5 11 181 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 181 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 181 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 9
  181 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 195 (accept_3_5 8 181
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 195
  (Polychromatic418967fa.accept_9_7_1_6_1_261 7 181 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 181 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 181 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 195 (accept_3_5 5 181 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 181 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 181 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3
  181 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 195 (accept_3_5 2 181
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 195
  (Polychromatic418967fa.accept_17_1_11_8_1_2725 1 181 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 181 195))))))))))))))) (allB_succ' 16 180 195 (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 195 15 1 12 13
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 180 195
  (Polychromatic418967fa.accept_19_14_9_5_1_9941 14 180 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 180 195 (Polychromatic418967fa.accept_19_13_9_5_1_8541 13 180 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 180 195 3 4 60 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 180 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  180 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 195 5 2 36 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 195 3 3 60 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 180 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 180 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 180 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 180 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180 195 3 2 60 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 180 195 5 1 36 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 180 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 180 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 180 195 3 1 60 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 180 195
  (Polychromatic418967fa.accept_17_2_10_8_1_7691 2 180 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 180 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 180 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 195)))))))))))))))) (allB_succ' 17 179 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 179 195 (accept_3_4 16 179 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 195 (Polychromatic418967fa.accept_21_15_11_6_1_5121 15 179 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 179 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 195 (accept_3_4 13 179 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 179 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 11 179 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 195 (accept_3_4 10 179 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 179 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 179 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 195 (accept_3_4 7 179 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 179 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 179 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 195 (accept_3_4 4 179 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 179 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 179 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 195 (accept_3_4 1 179 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 195))))))))))))))))) (allB_succ' 18 178 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 178 195 (accept_3_5 17 178 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 178 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 178 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 178 195 (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 178 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 178 195 (accept_3_5 14 178 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 178 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 178 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 178 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 178 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 178 195 (accept_3_5 11 178 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 178 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 178 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 178 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 178 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 178 195 (accept_3_5 8 178 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 178 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 178 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 178 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 178 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 178 195 (accept_3_5 5 178 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  178 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 178 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 178 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 178 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 195 (accept_3_5 2 178 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 178 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 195)))))))))))))))))) (allB_succ' 19 177 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 177 195 3 6 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 177 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 177 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 195
  (Polychromatic418967fa.accept_17_16_7_8_1_7638 16 177 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 177 195 3 5 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 177 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 177 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 177
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 195 3 4 59 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 177 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 177 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 195 3 3 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 177 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 177 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 177 195 3 2 59 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 177 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 177 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 177 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 195 3 1 59 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 177 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177 195))))))))))))))))))) (allB_succ' 20 176 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 176 195 (accept_3_4 19 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 176 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 176 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 176 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 176 195 (accept_3_4 16 176 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 176 195 (Polychromatic418967fa.accept_17_15_6_8_1_6343 15 176 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 176 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 176 195 (accept_3_4 13 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 176 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 176 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 176 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 176 195 (accept_3_4 10 176 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 176 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 176 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 176 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 176 195 (accept_3_4 7 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 195 (accept_3_4 4 176 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 176 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 195 (accept_3_4 1 176 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  195)))))))))))))))))))) (allB_succ' 21 175 195 (Eq.refl Bool.true) (allA_succ_of_gcd 20 175 195 5 4 35 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 175 195
  (Polychromatic418967fa.accept_9_1_4_6_1_5 19 175 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 175 195 (Polychromatic418967fa.accept_16_2_15_3_1_1300 18 175 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 195 (accept_3_5 17 175 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 175 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 175 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 175 195 5 3 35 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 175 195 (accept_3_5 14 175 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 175 195 (Polychromatic418967fa.accept_16_13_15_3_1_4196 13 175
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 175 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 175 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 175 195 (accept_3_5 11 175 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  175 195 5 2 35 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 175 195 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 175 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 175 195 (accept_3_5 8 175 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 175 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 175 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 195 (Polychromatic418967fa.accept_14_6_7_13_1_3158 6 175
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 175 195 5 1 35 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 175 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 175 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 175 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 195 (accept_3_5 2 175 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 175 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 175 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 195))))))))))))))))))))) (allB_succ' 22 174 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 174 195 3 7 58 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 20 174 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 174 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 174 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19
  174 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 174 195 3 6 58 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 174 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 174 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 174 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 174 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 174 195 3 5 58 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 174 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 14
  174 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 174 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 174 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 195 3 4 58 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 174 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 11 174 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 174 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 174 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 174 195 3 3 58 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 174 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 174 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 174 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 174 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 195 3 2 58 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 174 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 174 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 174 195 3 1 58 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 174 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 174 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 195)))))))))))))))))))))) (allB_succ' 23
  173 195 (Eq.refl Bool.true) (allA_succ_of_accept 22 173 195 (accept_3_4 22 173 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 173 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 173 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  173 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 173 195 (accept_3_4 19
  173 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 173 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 173 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 173 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 195 (accept_3_4 16 173 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 173 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 173 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  173 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 195 (accept_3_4 13
  173 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 195
  (Polychromatic418967fa.accept_9_3_2_6_1_264 12 173 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 173 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 173 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 195 (accept_3_4 10 173 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 173 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 173 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8
  173 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 195 (accept_3_4 7 173
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 173 195 (Polychromatic418967fa.accept_4_2_1_3_1_27
  6 173 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 5 173 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 173 195 (accept_3_4 4 173 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  173 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 173 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 173 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 173 195 (accept_3_4 1 173 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 173 195))))))))))))))))))))))) (allB_succ' 24 172 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 172 195 (accept_3_5 23 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 172 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 172 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 172 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 172 195 (accept_3_5 20 172 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 172 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 172 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 172 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 18 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 172 195 (accept_3_5 17 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 172 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 172 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 172 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 172 195 (accept_3_5 14 172 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 172 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 172 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 172 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 172 195 (accept_3_5 11 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 172 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 172 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 172 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 172 195 (accept_3_5 8 172 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 172 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 172 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 172 195 (accept_3_5 5 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  172 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 172 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 172 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 172 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 172 195 (accept_3_5 2 172 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 172 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 195)))))))))))))))))))))))) (allB_succ' 25 171 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 171 195 3 8 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 171 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 171 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 195
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 22 171 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 171 195 3 7 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 171 195 (Polychromatic418967fa.accept_21_20_3_6_1_8291 20 171 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 19 171
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 195 3 6 57 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 195
  (Polychromatic418967fa.accept_18_17_9_15_1_7268 17 171 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 171 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 171 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 171 195 3 5 57 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 171 195
  (Polychromatic418967fa.accept_10_4_1_5_1_1018 14 171 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 171 195 (Polychromatic418967fa.accept_20_13_11_15_1_6881 13 171 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 195 3 4 57 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 11 171 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 195 (Polychromatic418967fa.accept_14_10_3_13_1_1530 10 171 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 195 3 3 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 195 (Polychromatic418967fa.accept_16_8_11_3_1_4279
  8 171 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 195
  (Polychromatic418967fa.accept_16_7_11_3_1_1330 7 171 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 171 195 3 2 57 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 171 195 (Polychromatic418967fa.accept_18_5_9_15_1_4695 5 171 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 171 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 195 3 1 57 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 171 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 195 (Polychromatic418967fa.accept_21_1_3_6_1_8321 1 171 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171 195))))))))))))))))))))))))) (allB_succ' 26 170 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 170 195 5 5 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 170 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 170 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 170 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 170 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 170 195 (accept_3_4 22 170 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 170 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21
  170 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 170 195 5 4 34 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 170 195 (accept_3_4 19
  170 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 170 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 170 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 170 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 170 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 170 195 (accept_3_4 16 170 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 170 195 5 3 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 170 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 14 170 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 170 195 (accept_3_4 13 170 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 170 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 170 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 170 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 170 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 170 195 5 2 34 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 170 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 170 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 170 195 (accept_3_4 7 170 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 170 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6
  170 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 170 195 5 1 34 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 170 195 (accept_3_4 4
  170 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 170 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 170 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 2 170 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 170 195 (accept_3_4 1 170 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 170 195)))))))))))))))))))))))))) (allB_succ' 27 169 195 (Eq.refl Bool.true) (allA_succ_of_gcd
  26 169 195 13 2 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 25 169 195 (Polychromatic418967fa.accept_20_5_9_15_1_3973 25 169 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 169 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 169 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 195 (accept_3_5 23 169 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22
  169 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 195 (accept_3_5 20 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 169 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 195 (accept_3_5 17 169 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 169 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 195
  (Polychromatic418967fa.accept_19_15_17_5_1_3052 15 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 169 195 (accept_3_5 14 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 169 195 13 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 12 169 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 169 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 195 (accept_3_5 11 169 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 195 (accept_3_5 8 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 195 (accept_3_5 5 169 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 195 (accept_3_5 2 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 169 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 195))))))))))))))))))))))))))) (allB_succ' 28 168 195 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 168 195 3 9 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 168 195 (Polychromatic418967fa.accept_25_1_18_20_1_5828 26 168 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 168 195
  (Polychromatic418967fa.accept_20_5_8_15_1_9845 25 168 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 195 3 8 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 23 168 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 168 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 168
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 168 195 3 7 56 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 168 195
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 20 168 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 168 195 (Polychromatic418967fa.accept_23_19_7_11_1_6231 19 168 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 195 3 6 56 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 195
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 168 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 168 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 168 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 168 195 3 5 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 168 195
  (Polychromatic418967fa.accept_19_14_16_5_1_5668 14 168 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 168 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 168 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 195 3 4 56 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 195
  (Polychromatic418967fa.accept_16_11_8_3_1_3183 11 168 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 195 (Polychromatic418967fa.accept_17_10_15_8_1_6324 10 168 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 168 195 3 3 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 168 195 (Polychromatic418967fa.accept_19_8_16_5_1_8583
  8 168 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 195
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 7 168 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 195 3 2 56 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 168 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 195 (Polychromatic418967fa.accept_16_4_8_3_1_4206 4 168 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 195 3 1 56 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 195
  (Polychromatic418967fa.accept_10_2_8_5_1_587 2 168 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 195 (Polychromatic418967fa.accept_19_1_16_5_1_5671 1 168 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 195)))))))))))))))))))))))))))) (allB_succ' 29 167 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 28 167 195 (accept_3_4 28 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 167 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 167 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 167 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 195 (accept_3_4 25 167 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 195
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 24 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 167 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 23 167 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 195 (accept_3_4 22 167 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 167 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 167 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  167 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 195 (accept_3_4 19
  167 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 195
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 167 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 167 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 195 (accept_3_4 16 167 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 167 195 (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 167 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 195 (accept_3_4 13 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 167 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 195 (accept_3_4 10 167 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 167 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 195 (accept_3_4 7 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 195 (Polychromatic418967fa.accept_17_6_14_8_1_3858 6 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 5 167 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 195 (accept_3_4 4 167 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 167 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 195 (accept_3_4 1 167 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  195))))))))))))))))))))))))))))) (allB_succ' 30 166 195 (Eq.refl Bool.true) (allA_succ_of_accept 29 166 195
  (accept_3_5 29 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 166 195
  (Polychromatic418967fa.accept_9_1_4_6_1_5 28 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 166 195 (Polychromatic418967fa.accept_16_11_6_3_1_6564 27 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 166 195 (accept_3_5 26 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 166 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 166 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 166 195 (Polychromatic418967fa.accept_10_4_6_5_1_74
  24 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 166 195 (accept_3_5 23
  166 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 166 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 22 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 166 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 166 195 (accept_3_5 20 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 166 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 166 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 166 195 (Polychromatic418967fa.accept_7_4_5_6_1_344
  18 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 166 195 (accept_3_5 17
  166 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 166 195
  (Polychromatic418967fa.accept_9_7_4_6_1_273 16 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 166 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 195 (accept_3_5 14 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 166 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 195 (Polychromatic418967fa.accept_9_3_4_6_1_252
  12 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 166 195 (accept_3_5 11
  166 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 166 195
  (Polychromatic418967fa.accept_9_1_4_6_1_5 10 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 166 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 195 (accept_3_5 8 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 166 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 166 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313
  6 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 166 195 (accept_3_5 5
  166 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 166 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 166 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 166 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 195 (accept_3_5 2 166 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 166 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 195)))))))))))))))))))))))))))))) (allB_succ' 31 165 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 30 165 195 15 2 11 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 165 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 165 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 165 195 3 9 55 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 165 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 165 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 165 195 5 5 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 165 195 3 8 55 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 23
  165 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 165 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 195 3 7 55 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 165 195 5 4 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 165 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 165 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 195 3 6 55 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 17
  165 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 16 165 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 165 195 15 1 11 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 165 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 195 (Polychromatic418967fa.accept_9_4_3_6_1_532
  13 165 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 195 3 4 55 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 165 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 165 195 5 2 33 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 165 195 3 3 55 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 165 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 165 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 165 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 195 3 2 55 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 165 195 5 1 33 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 165 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 195 3 1 55 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 165 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 195)))))))))))))))))))))))))))))))
  (allB_succ' 32 164 195 (Eq.refl Bool.true) (allA_succ_of_accept 31 164 195 (accept_3_4 31 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 164 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 164 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 164 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 164 195 (accept_3_4 28 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 164 195 (Polychromatic418967fa.accept_19_8_12_5_1_7122 27 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 164 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 164 195 (accept_3_4 25 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 164 195 (Polychromatic418967fa.accept_16_8_4_3_1_3146 24 164 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 164 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 164 195 (accept_3_4 22 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 164 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 164 195 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 164 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 164 195 (accept_3_4 19 164 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 164 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 164 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 164 195 (accept_3_4 16 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 164 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 164 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 195 (accept_3_4 13 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 164 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 164 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 164 195 (accept_3_4 10 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  164 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 164 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 195 (accept_3_4 7 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 164 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 164 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 164 195 (accept_3_4 4 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  164 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 164 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 164 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 195 (accept_3_4 1 164 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 195)))))))))))))))))))))))))))))))) (allB_succ' 33 163 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 32 163 195 (accept_3_5 32 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 163 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 163 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 30 163 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 163 195 (accept_3_5 29 163 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 163 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 163 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 163 195
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 163 195 (accept_3_5 26 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 163 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 163 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 163 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 163 195 (accept_3_5 23 163 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 163 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 163 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 163 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 21 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 163 195 (accept_3_5 20 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 163 195 (Polychromatic418967fa.accept_17_2_10_8_1_7691 19 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 163 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 163 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 195 (accept_3_5 17 163 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 195 (accept_3_5 14 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 12 163 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 195 (accept_3_5 11 163 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 163 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 195
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 195 (accept_3_5 8 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 195 (Polychromatic418967fa.accept_19_6_11_5_1_5628 6 163 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 195 (accept_3_5 5 163 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 195 (accept_3_5 2 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 163 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 195))))))))))))))))))))))))))))))))) (allB_succ' 34 162 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 33 162 195 3 11 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 162 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 32 162 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 162 195
  (Polychromatic418967fa.accept_16_15_2_3_1_4262 31 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 195 3 10 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 162 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 162 195 (Polychromatic418967fa.accept_10_8_2_5_1_596
  28 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 162 195 3 9 54 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 162 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 162 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 162 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 162 195 3 8 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 162 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 23
  162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 162 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 162 195 3 7 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 162 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 162 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 162 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 162 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 195 3 6 54 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 162 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 162 195 3 5 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 162 195 (Polychromatic418967fa.accept_12_2_6_3_1_331
  14 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 195 3 4 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 162 195 (Polychromatic418967fa.accept_17_11_9_8_1_5038 11 162 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 195 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 162
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 162 195 3 3 54 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 162 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 162 195 (Polychromatic418967fa.accept_10_7_2_5_1_298 7 162 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 195 3 2 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 195
  (Polychromatic418967fa.accept_12_4_6_3_1_332 4 162 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 162 195 3 1 54 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 162 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 162 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 195))))))))))))))))))))))))))))))))))
  (allB_succ' 35 161 195 (Eq.refl Bool.true) (allA_succ_of_accept 34 161 195 (accept_3_4 34 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 161 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 195 (accept_3_4 31 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 195 (accept_3_4 28 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 195 (Polychromatic418967fa.accept_18_9_17_15_1_2267 27 161 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 195 (accept_3_4 25 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 195 (accept_3_4 22 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 161 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 195 (accept_3_4 19 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 195 (Polychromatic418967fa.accept_22_17_7_19_1_11358 17 161 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 195 (accept_3_4 16 161 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 161
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 195 (accept_3_4 13 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 195 (accept_3_4 10 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 161 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 195 (accept_3_4 7 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 195 (accept_3_4 4 161 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 161 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 195 (accept_3_4 1 161 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  195))))))))))))))))))))))))))))))))))) (allB_succ' 36 160 195 (Eq.refl Bool.true) (allA_succ_of_gcd 35 160 195 5 7 32
  39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 160 195
  (Polychromatic418967fa.accept_22_12_6_19_1_8159 34 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 160 195 (Polychromatic418967fa.accept_14_5_6_13_1_3145 33 160 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 160 195 (accept_3_5 32 160 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 160 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 160 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 160 195 5 6 32 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 160 195 (accept_3_5 29
  160 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 160 195
  (Polychromatic418967fa.accept_9_1_7_6_1_75 28 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 160 195 (Polychromatic418967fa.accept_18_9_16_15_1_2241 27 160 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 160 195 (accept_3_5 26 160 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 25 160 195 5 5 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 160 195 (Polychromatic418967fa.accept_18_6_16_15_1_7287 24 160
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 160 195 (accept_3_5 23 160
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 195
  (Polychromatic418967fa.accept_9_4_7_6_1_255 22 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 160 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 160 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 160 195 5 4 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 160 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 160 195 (accept_3_5 17 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 160 195 (Polychromatic418967fa.accept_17_16_7_8_1_7638 16 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 160 195 5 3 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 160 195 (accept_3_5 14 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 160 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 160 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 195 (accept_3_5 11 160 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 160 195 5 2 32 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 160 195
  (Polychromatic418967fa.accept_18_9_16_15_1_2241 9 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 160 195 (accept_3_5 8 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  160 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 160 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 160 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 160 195 5 1 32 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 160 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 4
  160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 160 195 (accept_3_5 2 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  160 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 160 195)))))))))))))))))))))))))))))))))))) (allB_succ' 37 159 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 159 195 3 12 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 159 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 159 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 195 (Polychromatic418967fa.accept_10_4_9_5_1_84
  34 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 159 195 3 11 53 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 159 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 159 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 195 3 10 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 29
  159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 28 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 159 195 3 9 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 159 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 26 159 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 159 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 159 195 3 8 53 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 159 195
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 23 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 159 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 195 3 7 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 20
  159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 195
  (Polychromatic418967fa.accept_21_19_12_6_1_6689 19 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 159 195 3 6 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 159 195 (Polychromatic418967fa.accept_19_17_7_5_1_1883 17 159 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 195
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 16 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 159 195 3 5 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 159 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 14 159 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 13 159
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 195 3 4 53 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 195 (Polychromatic418967fa.accept_19_10_7_5_1_5653 10 159 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 195 3 3 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 159 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 195
  (Polychromatic418967fa.accept_16_7_15_3_1_1302 7 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 195 3 2 53 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 195 (Polychromatic418967fa.accept_20_5_19_15_1_3946 5 159 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 159 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 195 3 1 53 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 195
  (Polychromatic418967fa.accept_11_2_5_8_1_470 2 159 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 159 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159 195))))))))))))))))))))))))))))))))))))) (allB_succ' 38 158 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 195 (accept_3_4 37 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 158 195 (Polychromatic418967fa.accept_20_16_18_15_1_11357 36 158 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 158 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35
  158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 158 195 (accept_3_4 34
  158 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 158 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 158 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 32 158 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 158 195 (accept_3_4 31 158 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 158 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 158 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 158 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 158 195 (accept_3_4 28
  158 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 158 195
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 158 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 158 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 158 195 (accept_3_4 25 158 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 158 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 158 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 158 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23
  158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 195 (accept_3_4 22
  158 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 158 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 20 158 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 158 195 (accept_3_4 19 158 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 158 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 158 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 158 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 158 195 (accept_3_4 16 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 158 195 (Polychromatic418967fa.accept_19_15_6_5_1_4356 15 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 158 195 (Polychromatic418967fa.accept_19_14_6_5_1_9917 14 158 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 158 195 (accept_3_4 13 158 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 158 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 158 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 158 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 158 195 (accept_3_4 10 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  158 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 158 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 158 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 158 195 (accept_3_4 7 158 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 158 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 158 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 158 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 158 195 (accept_3_4 4 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  158 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 158 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 158 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 158 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 158 195 (accept_3_4 1 158 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 158 195)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 157 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 38 157 195 (accept_3_5 38 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 157 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 37 157 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 157 195 (Polychromatic418967fa.accept_21_15_10_6_1_11306 36
  157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 157 195 (accept_3_5 35
  157 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 157 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 157 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 157 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 195 (accept_3_5 32 157 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 157 195 (Polychromatic418967fa.accept_16_15_13_3_1_4215 31 157 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 157 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 157 195 (accept_3_5 29 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 157 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 157 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 157 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 157 195 (accept_3_5 26 157 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 157 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 195
  (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 157 195 (accept_3_5 23 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 157 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 157 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 157 195 (accept_3_5 20 157 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 157 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 19
  157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 157 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 157 195 (accept_3_5 17 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 157 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 157 195 (Polychromatic418967fa.accept_16_15_13_3_1_4215 15 157 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 157 195 (accept_3_5 14 157 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 157 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 13 157
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 157 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 157 195 (accept_3_5 11 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 157 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 157 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 157 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 157 195 (accept_3_5 8 157 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 157 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 157 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 157 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 157 195 (accept_3_5 5 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  157 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 157 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 157 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 157 195 (accept_3_5 2 157 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 157 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 157 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 157 195)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 156 195 (Eq.refl Bool.true) (allA_succ_of_gcd 39 156 195 39 1 4 5 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 156 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 156 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 156 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 156 195 3 12 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 156 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 156 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 156 195 3 11 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 156 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 156 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 156 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 31
  156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 195 3 10 52 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 156 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 28 156 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 156 195 3 9 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 195 13 2 12 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 25 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 195 3 8 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 156 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 156 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 156 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 156 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 156 195 3 7 52 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 156 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 20 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 156 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 156 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 156 195 3 6 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 156 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 17
  156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 156 195 3 5 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 156 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 156 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 156 195 13 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 12 156 195 3 4 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 11
  156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 156 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 156 195 3 3 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 156 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 156 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 156 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 195 3 2 52 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 156 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 156 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 195 3 1 52 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 156 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 156 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 1 156 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 195)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 155 195 (Eq.refl Bool.true) (allA_succ_of_gcd
  40 155 195 5 8 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 155 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 155 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 155 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 155 195 (accept_3_4 37 155 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 195
  (Polychromatic418967fa.accept_19_17_3_5_1_3088 36 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 155 195 5 7 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 155 195 (accept_3_4 34 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 155 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 195 (accept_3_4 31 155 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 30 155 195 5 6 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 155 195 (Polychromatic418967fa.accept_19_10_3_5_1_11346 29 155
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 195 (accept_3_4 28 155
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 195
  (Polychromatic418967fa.accept_17_10_2_8_1_6295 27 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 155 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 155 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 155 195 5 5 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 155 195 (Polychromatic418967fa.accept_16_8_11_3_1_4279
  24 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 195 (accept_3_4 22 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 155 195 5 4 31 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 155 195 (accept_3_4 19 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 155 195 (Polychromatic418967fa.accept_22_18_1_19_1_6422 18 155 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 195 (Polychromatic418967fa.accept_9_8_2_6_1_875
  17 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 195 (accept_3_4 16
  155 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 155 195 5 3 31 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 155 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 195 (accept_3_4 13 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 195 (Polychromatic418967fa.accept_17_11_2_8_1_7569 11 155 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 155 195 5 2 31 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 155 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 155 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 195 (accept_3_4 7 155 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 155 195 (Polychromatic418967fa.accept_16_6_11_3_1_2198 6 155 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 155 195 5 1 31 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 155 195 (accept_3_4 4 155 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 155 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 195 (accept_3_4 1 155 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  195))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 154 195 (Eq.refl Bool.true) (allA_succ_of_accept 41 154
  195 (accept_3_5 41 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 154 195
  (Polychromatic418967fa.accept_9_4_1_6_1_284 40 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 154 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 154 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 154 195 (accept_3_5 38 154 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 154 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 154 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 154 195 (Polychromatic418967fa.accept_10_6_4_5_1_615
  36 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 154 195 (accept_3_5 35
  154 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 154 195
  (Polychromatic418967fa.accept_9_7_1_6_1_261 34 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 154 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 154 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 154 195 (accept_3_5 32 154 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 154 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 154 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 154 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 30
  154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 154 195 (accept_3_5 29
  154 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 154 195
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 28 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 154 195 (Polychromatic418967fa.accept_18_9_10_15_1_7254 27 154 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 195 (accept_3_5 26 154 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 195
  (Polychromatic418967fa.accept_17_7_1_8_1_6280 24 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 195 (accept_3_5 23 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 195 (accept_3_5 20 154 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 154 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 195 (accept_3_5 17 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 195 (Polychromatic418967fa.accept_24_15_10_3_1_11356 15 154 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 195 (accept_3_5 14 154 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 154 195 (accept_3_5 11 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 154 195 (Polychromatic418967fa.accept_19_10_2_5_1_3059 10 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 154 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 154 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 195 (accept_3_5 8 154 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 154 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 195
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 195 (accept_3_5 5 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 154 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 154 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 195 (accept_3_5 2 154 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 195))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 153 195 (Eq.refl Bool.true) (allA_succ_of_gcd 42 153 195 3 14 51 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 153 195
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 195 (Polychromatic418967fa.accept_18_4_9_15_1_3383 40 153 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 153 195 3 13 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 153 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 195
  (Polychromatic418967fa.accept_10_7_3_5_1_301 37 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 153 195 3 12 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 153 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 153 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 153 195 3 11 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 153 195 (Polychromatic418967fa.accept_10_2_3_5_1_996 32 153 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 153 195 (Polychromatic418967fa.accept_11_9_10_8_1_444
  31 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 195 3 10 51 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 195
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 195 (Polychromatic418967fa.accept_10_8_3_5_1_613 28 153 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 195 3 9 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 195
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 153 195 3 8 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 153 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 153 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 195 3 7 51 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 195
  (Polychromatic418967fa.accept_11_9_10_8_1_444 20 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 153 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 195 3 6 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 195 (Polychromatic418967fa.accept_10_7_3_5_1_301
  17 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 195
  (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 153 195 3 5 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 153 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 195
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 153 195 3 4 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 153 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 153 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 195 3 3 51 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 195
  (Polychromatic418967fa.accept_10_8_3_5_1_613 8 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 153 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 153 195 3 2 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 153 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 153 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 195
  (Polychromatic418967fa.accept_18_4_9_15_1_3383 4 153 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 153 195 3 1 51 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 153 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 153 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  195))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 152 195 (Eq.refl Bool.true) (allA_succ_of_accept 43 152
  195 (accept_3_4 43 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 152 195
  (Polychromatic418967fa.accept_12_6_8_3_1_82 42 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 152 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 152 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 152 195 (accept_3_4 40 152 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 152 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 152 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 38
  152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 152 195 (accept_3_4 37
  152 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 152 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 152 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 152 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 152 195 (accept_3_4 34 152 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 152 195 (Polychromatic418967fa.accept_10_3_2_5_1_295 33 152 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 152 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 152 195 (accept_3_4 31 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 152 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 152 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 195 (accept_3_4 28 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 195 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 152 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 195
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 26 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 152 195 (accept_3_4 25 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 152 195 (Polychromatic418967fa.accept_17_7_16_8_1_7613 24 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 152 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 195 (accept_3_4 22 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 152 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 195 (accept_3_4 19 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 195 (accept_3_4 16 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 152 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 195 (accept_3_4 13 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 195 (accept_3_4 10 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 195 (Polychromatic418967fa.accept_17_9_16_8_1_2721 9 152 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 195 (accept_3_4 7 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 195 (accept_3_4 4 152 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 152 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 2 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 195 (accept_3_4 1 152 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  195)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 151 195 (Eq.refl Bool.true) (allA_succ_of_accept 44 151
  195 (accept_3_5 44 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 151 195
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 43 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 151 195 (Polychromatic418967fa.accept_16_10_7_3_1_6601 42 151 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 151 195 (accept_3_5 41 151 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 151 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 39
  151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 151 195 (accept_3_5 38
  151 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 151 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 37 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 151 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 151 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 195 (accept_3_5 35 151 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 151 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 195 (Polychromatic418967fa.accept_7_5_4_6_1_167
  33 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 151 195 (accept_3_5 32
  151 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 151 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 151 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 195 (accept_3_5 29 151 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 151 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 195
  (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 195 (accept_3_5 26 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 195 (Polychromatic418967fa.accept_16_9_7_3_1_614 25 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 195 (accept_3_5 23 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 151 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 151 195 (accept_3_5 20 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 151 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 151 195 (Polychromatic418967fa.accept_21_18_4_6_1_6697 18 151 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 195 (accept_3_5 17 151 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 195
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 15 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 151 195 (accept_3_5 14 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 151 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 151 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 195 (accept_3_5 11 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 151 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 151 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 151 195 (accept_3_5 8 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  151 195 (Polychromatic418967fa.accept_21_7_4_6_1_11287 7 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 151 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 195 (accept_3_5 5 151 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 151 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 3 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 151 195 (accept_3_5 2 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  151 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 151 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 151 195))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 150 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 150 195 15 3 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 150 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 150 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 150 195
  (Polychromatic418967fa.accept_16_11_6_3_1_6564 43 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 195 3 14 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 150 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 195 5 8 30 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 150 195 3 13 50 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 150 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 38 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 150 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 150 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 195 3 12 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 150 195 5 7 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 150 195 (Polychromatic418967fa.accept_12_10_6_3_1_786
  34 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 150 195 3 11 50 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 150 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 195 (Polychromatic418967fa.accept_14_3_10_13_1_339 31 150 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 195 15 2 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 195
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 150 195 3 9 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 150 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 26 150 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 150 195 5 5 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 150 195 3 8 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23
  150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 150 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 22 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 150 195 3 7 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 150 195 5 4 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 150 195 (Polychromatic418967fa.accept_20_19_10_15_1_1529 19 150 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 195 3 6 50 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 150 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 150 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 195 15 1 10 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 195 (Polychromatic418967fa.accept_12_2_6_3_1_331
  14 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 150 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 195 3 4 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 150 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 150 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 195 5 2 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 195 3 3 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 150 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 8
  150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 195
  (Polychromatic418967fa.accept_17_7_14_8_1_5069 7 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 195 3 2 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 150 195 5 1 30 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 150 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 150 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 150 195 3 1 50 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 150 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 150 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 195)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 149 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 149 195 (accept_3_4 46 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 195 (accept_3_4 43 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 149 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 41 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 195 (accept_3_4 40 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 195 (accept_3_4 37 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 149 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 195 (accept_3_4 34 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 195 (accept_3_4 31 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 195 (accept_3_4 28 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 195 (Polychromatic418967fa.accept_18_9_5_15_1_2246 27 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 195 (accept_3_4 25 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 149 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 195
  (Polychromatic418967fa.accept_20_3_9_15_1_6847 23 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 149 195 (accept_3_4 22 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 149 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 149 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 195 (accept_3_4 19 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 149 195 (accept_3_4 16 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 149 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 149 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 195 (accept_3_4 13 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 149 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 195 (accept_3_4 10 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 195 (accept_3_4 7 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 195
  (Polychromatic418967fa.accept_17_5_13_8_1_7556 5 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 195 (accept_3_4 4 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 149 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 195 (accept_3_4 1 149 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 195))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 148 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 148 195 (accept_3_5 47 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 148 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 148 195 (Polychromatic418967fa.accept_18_9_4_15_1_555 45 148
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 148 195 (accept_3_5 44 148
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 148 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 148 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 148 195 (accept_3_5 41 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 148 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 148 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 148 195 (Polychromatic418967fa.accept_8_7_4_3_1_156
  39 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 148 195 (accept_3_5 38
  148 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 148 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 37 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 148 195 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 148 195 (accept_3_5 35 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 148 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 148 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 148 195 (Polychromatic418967fa.accept_7_5_1_6_1_163
  33 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 195 (accept_3_5 32
  148 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 148 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 148 195 (accept_3_5 29 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 148 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 148 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 148 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008
  27 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 195 (accept_3_5 26
  148 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 148 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 148 195 (accept_3_5 23 148 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 148 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 148 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 148 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 148 195 (accept_3_5 20 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 148 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 148 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 18 148 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 148 195 (accept_3_5 17 148 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 148 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 148 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 148 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 15 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 148 195 (accept_3_5 14 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 148 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 148 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 148 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 148 195 (accept_3_5 11 148 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 148 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 10 148 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 148 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 148 195 (accept_3_5 8 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  148 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 148 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 148 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 148 195 (accept_3_5 5 148 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 148 195 (Polychromatic418967fa.accept_17_4_12_8_1_3833 4 148 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 148 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 148 195 (accept_3_5 2 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  148 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 148 195)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 147 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 147 195 3 16 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 147 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 147 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 147 195 3 15 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 147 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 147 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 195 (Polychromatic418967fa.accept_9_7_3_6_1_270
  43 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 147 195 3 14 49 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 41 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 147 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 195 3 13 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 37 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 147 195 3 12 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 147 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 147 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 195 (Polychromatic418967fa.accept_9_7_3_6_1_270
  34 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 147 195 3 11 49 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 147 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 147 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 147 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 147 195 3 10 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 147 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 147 195 3 9 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 147 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 147 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 25 147 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 195 3 8 49 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 147 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 195 3 7 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 147 195 3 6 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 147 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 17 147 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 147 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 195 3 5 49 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 147 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 147 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 147 195 3 4 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 147 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 195 3 3 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 147 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 147 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 195 3 2 49 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 5 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 147 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 195 3 1 49 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 147 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 1 147 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 195))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 146 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 146 195 (accept_3_4 49 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 146 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 146 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 146 195 (accept_3_4 46 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 146 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 146 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 146 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 146 195 (accept_3_4 43 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 146 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 146 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 146 195 (accept_3_4 40 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 146 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 146 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 146 195
  (Polychromatic418967fa.accept_11_5_3_8_1_454 38 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 146 195 (accept_3_4 37 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 146 195 (Polychromatic418967fa.accept_17_2_10_8_1_7691 36 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 146 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 195 (accept_3_4 34 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 146 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 32 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 146 195 (accept_3_4 31 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 146 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 146 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 195 (accept_3_4 28 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 146 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 146 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 26 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 195 (accept_3_4 25 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 24 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 195 (accept_3_4 22 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 195
  (Polychromatic418967fa.accept_23_20_8_11_1_11355 20 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 146 195 (accept_3_4 19 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 146 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 146 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 146 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 195 (accept_3_4 16 146 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 195
  (Polychromatic418967fa.accept_16_15_2_3_1_4262 15 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 146 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 146 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 146 195 (accept_3_4 13 146 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 146 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 146 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 195 (accept_3_4 10
  146 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 146 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 8 146 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 146 195 (accept_3_4 7 146 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 146 195 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 146 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 146 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5
  146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 195 (accept_3_4 4 146
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 195
  (Polychromatic418967fa.accept_9_3_2_6_1_264 3 146 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 146 195 (Polychromatic418967fa.accept_17_2_10_8_1_7691 2 146 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 146 195 (accept_3_4 1 146 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 146 195)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 145 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 145 195 5 10 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 145 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 145 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 145 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 145 195 (accept_3_5 47 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 145 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 145 195 5 9 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 145 195 (accept_3_5 44 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 145 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 145 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 145 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 145 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 195 (accept_3_5 41 145 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 145 195 5 8 29 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 145 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 145 195 (accept_3_5 38 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 145 195 (Polychromatic418967fa.accept_20_17_5_15_1_6912 37 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 145 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 145 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 145 195 5 7 29 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 145 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 145 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 145 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 195 (accept_3_5 32 145 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 145 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 145 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 145 195 5 6 29 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 145 195 (accept_3_5 29 145 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 145 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 195
  (Polychromatic418967fa.accept_11_5_2_8_1_866 27 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 195 (accept_3_5 26 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25
  145 195 5 5 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  24 145 195 (Polychromatic418967fa.accept_20_4_5_15_1_6869 24 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 145 195 (accept_3_5 23 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 145 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 145 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 145 195 5 4 29 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 145 195
  (Polychromatic418967fa.accept_20_19_5_15_1_5380 19 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 195 (accept_3_5 17 145 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 145 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 145 195 5 3 29 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 145 195 (accept_3_5 14 145 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 195 (Polychromatic418967fa.accept_9_4_1_6_1_284
  13 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 145 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 145 195 (accept_3_5 11 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  145 195 5 2 29 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 145 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 145 195 (accept_3_5 8 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 145 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 145 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 145 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 145 195 5 1 29 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 145 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 145 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 145 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 195 (accept_3_5 2 145 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 145 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 145 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 145 195)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 144 195 (Eq.refl Bool.true) (allA_succ_of_gcd 51 144 195 3 17 48 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 144 195
  (Polychromatic418967fa.accept_19_12_11_5_1_950 50 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 144 195 (Polychromatic418967fa.accept_10_9_4_5_1_616 49 144 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 144 195 3 16 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 144 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 144 195
  (Polychromatic418967fa.accept_10_6_4_5_1_615 46 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 144 195 3 15 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 144 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 144 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 144 195
  (Polychromatic418967fa.accept_23_20_6_11_1_6229 43 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 144 195 3 14 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 144 195 (Polychromatic418967fa.accept_10_1_4_5_1_1031 41 144 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 144 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 144 195 3 13 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 144 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 144 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 195 (Polychromatic418967fa.accept_7_2_4_6_1_166
  37 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 195 3 12 48 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 195
  (Polychromatic418967fa.accept_19_16_11_5_1_11315 35 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 144 195 (Polychromatic418967fa.accept_19_15_11_5_1_5713 34 144 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 144 195 3 11 48 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 144 195
  (Polychromatic418967fa.accept_19_13_11_5_1_5692 32 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 144 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 144 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 195 3 10 48 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 195
  (Polychromatic418967fa.accept_10_9_4_5_1_616 29 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 144 195 (Polychromatic418967fa.accept_21_7_18_6_1_9797 28 144 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 144 195 3 9 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 144 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 26
  144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 195
  (Polychromatic418967fa.accept_19_6_11_5_1_5628 25 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 195 3 8 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 144 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 195 (Polychromatic418967fa.accept_20_2_4_15_1_6911 22 144
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 144 195 3 7 48 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 144 195
  (Polychromatic418967fa.accept_21_20_18_6_1_5094 20 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 144 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 144 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 195 3 6 48 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 144 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 144 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 144 195 3 5 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 144 195
  (Polychromatic418967fa.accept_19_14_11_5_1_11302 14 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 144 195 (Polychromatic418967fa.accept_19_13_11_5_1_5692 13 144 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 195 3 4 48 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 195
  (Polychromatic418967fa.accept_10_1_4_5_1_1031 11 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 144 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 144 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 144 195 3 3 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 144 195 (Polychromatic418967fa.accept_27_8_9_6_1_11354 8 144 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 144 195
  (Polychromatic418967fa.accept_21_7_18_6_1_9797 7 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 144 195 3 2 48 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 144 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 195 (Polychromatic418967fa.accept_11_4_1_8_1_1366 4 144 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 144 195 3 1 48 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 144 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 144 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 144 195 (Polychromatic418967fa.accept_10_1_4_5_1_1031 1 144 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144 195)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  143 195 (Eq.refl Bool.true) (allA_succ_of_gcd 52 143 195 13 4 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 143 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 143 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 195 (accept_3_4 49 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 195 (accept_3_4 46 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 143 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 195 (accept_3_4 43 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 195 (Polychromatic418967fa.accept_10_2_3_5_1_996 42 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 195 (accept_3_4 40 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 39 143 195 13 3 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 143 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 143 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 195 (accept_3_4 37 143 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 143 195 (Polychromatic418967fa.accept_8_4_7_3_1_144
  36 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 195
  (Polychromatic418967fa.accept_17_1_7_8_1_6347 35 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 195 (accept_3_4 34 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 195 (accept_3_4 31 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 143 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 29 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 195 (accept_3_4 28 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 143 195 13 2 11 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 143 195 (accept_3_4 25 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 143 195 (Polychromatic418967fa.accept_14_10_3_13_1_1530 24 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23
  143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 195 (accept_3_4 22
  143 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 195
  (Polychromatic418967fa.accept_9_3_8_6_1_80 21 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 143 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 143 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 195 (accept_3_4 19 143 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 143 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 195 (Polychromatic418967fa.accept_10_7_3_5_1_301
  17 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 195 (accept_3_4 16
  143 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 195
  (Polychromatic418967fa.accept_19_15_10_5_1_5637 15 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 143 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 13 143 195 13 1 11 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 12 143 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 143 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 143 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 195 (accept_3_4 10 143 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 143 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8
  143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 195 (accept_3_4 7 143
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 195
  (Polychromatic418967fa.accept_18_6_17_15_1_4603 6 143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 143 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 143 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 195 (accept_3_4 4 143 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 143 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 143 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 2
  143 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 195 (accept_3_4 1 143
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143 195)))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 54 142 195 (Eq.refl Bool.true) (allA_succ_of_accept 53 142 195 (accept_3_5 53 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 142 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 142 195
  (Polychromatic418967fa.accept_19_13_9_5_1_8541 51 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 142 195 (accept_3_5 50 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 142 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 142 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 142 195 (accept_3_5 47 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 142 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 142 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 45 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 142 195 (accept_3_5 44 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 142 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 142 195 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 142 195 (accept_3_5 41 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 142 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 142 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 142 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 142 195 (accept_3_5 38 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 142 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 142 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 142 195 (accept_3_5 35 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 142 195 (Polychromatic418967fa.accept_19_15_9_5_1_5656 34 142 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 142 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 142 195 (accept_3_5 32 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 142 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 142 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 30 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 142 195 (accept_3_5 29 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 142 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 142 195
  (Polychromatic418967fa.accept_10_7_2_5_1_298 27 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 142 195 (accept_3_5 26 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 142 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 142 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 142 195 (accept_3_5 23 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 142 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 142 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 142 195 (accept_3_5 20 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 142 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 142 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 142 195 (accept_3_5 17 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 142 195 (Polychromatic418967fa.accept_23_16_4_11_1_11353 16 142 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 142 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 142 195 (accept_3_5 14 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 142 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 142 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 142 195 (accept_3_5 11 142 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 142 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 10 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 142 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 142 195 (accept_3_5 8 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  142 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 142 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 142 195 (accept_3_5 5 142 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 142 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 142 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 142 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 142 195 (accept_3_5 2 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  142 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 142 195)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 141 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 141 195 3 18 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 141 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 53 141 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 195
  (Polychromatic418967fa.accept_19_14_8_5_1_8606 52 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 141 195 3 17 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 141 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 141 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 195 (Polychromatic418967fa.accept_10_9_1_5_1_594
  49 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 141 195 3 16 47 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 141 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 47 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 141 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 141 195 3 15 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 141 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 44
  141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 195
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 43 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 141 195 3 14 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 141 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 141 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 195 (Polychromatic418967fa.accept_7_5_1_6_1_163
  40 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 195 3 13 47 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 141 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 141 195 3 12 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 141 195 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 141 195 3 11 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 141 195 (Polychromatic418967fa.accept_11_10_9_8_1_1974 32 141 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 141 195 3 10 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 141 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 141 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 195
  (Polychromatic418967fa.accept_22_6_9_19_1_11352 28 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 141 195 3 9 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 141 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 195
  (Polychromatic418967fa.accept_12_1_9_3_1_370 25 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 195 3 8 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 141 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 195 3 7 47 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 195
  (Polychromatic418967fa.accept_17_3_5_8_1_1687 20 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 141 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 195 3 6 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 195 3 5 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 141
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 195 3 4 47 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 195
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 195 3 3 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 195 (Polychromatic418967fa.accept_16_8_13_3_1_4253 8 141 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 195 3 2 47 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 141 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 4 141 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 195 3 1 47 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 141 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 195))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  56 140 195 (Eq.refl Bool.true) (allA_succ_of_gcd 55 140 195 5 11 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 140 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 54
  140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 140 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 53 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 140 195 (accept_3_4 52 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 140 195 (Polychromatic418967fa.accept_19_13_7_5_1_5712 51 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 140 195 5 10 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 140 195 (accept_3_4 49 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 140 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 140 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 140 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 140 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 140 195 (accept_3_4 46 140 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 140 195 5 9 28 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 140 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 140 195 (accept_3_4 43 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 140 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 195 5 8 28 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 39 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 140 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 140 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 140 195 (accept_3_4 37 140 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 140 195 (Polychromatic418967fa.accept_16_4_12_3_1_2180 36 140 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 140 195 5 7 28 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 140 195 (accept_3_4 34 140 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 195
  (Polychromatic418967fa.accept_21_12_14_6_1_8214 33 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 140 195 (Polychromatic418967fa.accept_19_13_7_5_1_5712 32 140 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 140 195 (accept_3_4 31 140 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 195 5 6 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 29
  140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 195 (accept_3_4 28
  140 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 195
  (Polychromatic418967fa.accept_22_5_8_19_1_11307 27 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 140 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 26 140 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 140 195 5 5 28 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 140 195
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 140 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 195 (accept_3_4 22 140 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 140 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 140 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 195 5 4 28 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 195 (accept_3_4 19 140 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 140 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 140 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 140 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 140 195 (accept_3_4 16 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  140 195 5 3 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 140 195 (Polychromatic418967fa.accept_23_14_2_11_1_11351 14 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 140 195 (accept_3_4 13 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 140 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 140 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 140 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 195 5 2 28 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 195
  (Polychromatic418967fa.accept_16_9_12_3_1_3138 9 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 140 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 8 140 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 195 (accept_3_4 7 140 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 140 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 140 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 140 195 5 1 28 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 140 195 (accept_3_4 4 140 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 140 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 140 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 140 195 (accept_3_4 1 140 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 139 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 56 139 195 (accept_3_5 56 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 139 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 139 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 139 195 (accept_3_5 53 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 51 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 139 195 (accept_3_5 50 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 139 195 (Polychromatic418967fa.accept_19_11_6_5_1_11299 49 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 195 (accept_3_5 47 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 195
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 195 (accept_3_5 44 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 43 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 195 (Polychromatic418967fa.accept_19_4_6_5_1_11350 42 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 195 (accept_3_5 41 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 139 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 195 (accept_3_5 38 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 195 (accept_3_5 35 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 139 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 195
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 195 (accept_3_5 32 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 31 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 195 (accept_3_5 29 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 195
  (Polychromatic418967fa.accept_25_2_14_20_1_11349 27 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 139 195 (accept_3_5 26 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 139 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 25 139 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 139 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 195 (accept_3_5 23 139 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22
  139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 195 (accept_3_5 20 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 195 (Polychromatic418967fa.accept_19_18_6_5_1_4321 18 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 195 (accept_3_5 17 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 195
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 195 (accept_3_5 14 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 195 (Polychromatic418967fa.accept_17_13_3_8_1_6310 13 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 195 (accept_3_5 11 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 195
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 195 (accept_3_5 8 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 195 (accept_3_5 5 139 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 195 (accept_3_5 2 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 1 139 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 138 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 138 195 3 19 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 56 138 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 138 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 138 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 195 3 18 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 138 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 138 195 (Polychromatic418967fa.accept_9_7_3_6_1_270
  52 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 138 195 3 17 46 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 138 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 138 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 138 195 3 16 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 138 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 47
  138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 138 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 46 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 138 195 3 15 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 138 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 44 138 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 43
  138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 195 3 14 46 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 138 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 40 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 138 195 3 13 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 138 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 38
  138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 195 3 12 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 138 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 195 (Polychromatic418967fa.accept_9_7_3_6_1_270
  34 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 138 195 3 11 46 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 138 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 138 195 3 10 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 138 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 138 195 3 9 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 138 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 26 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 195 3 8 46 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 23 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 138 195 3 7 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 138 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 19 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 195 3 6 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 16 138 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 138 195 3 5 46 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 138 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 195 3 4 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 11
  138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 10 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 138 195 3 3 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 138 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 138 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 195 3 2 46 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 138 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 138 195 3 1 46 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 2 138 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 137 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 137 195 (accept_3_4 58 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 137 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 137 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 137 195 (accept_3_4 55 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 137 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 137 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 53 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 137 195 (accept_3_4 52 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 137 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 137 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 137 195 (accept_3_4 49 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 137 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 137 195 (accept_3_4 46 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 195 (accept_3_4 43 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 195
  (Polychromatic418967fa.accept_9_5_2_6_1_265 41 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 195 (accept_3_4 40 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 195 (accept_3_4 37 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 195 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 35 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 195 (accept_3_4 34 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 195 (accept_3_4 31 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 195
  (Polychromatic418967fa.accept_25_4_12_20_1_11348 29 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 137 195 (accept_3_4 28 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 137 195 (Polychromatic418967fa.accept_18_9_11_15_1_4616 27 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 195 (accept_3_4 25
  137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 137 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 137 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 195 (accept_3_4 22 137 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 137 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20
  137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 195 (accept_3_4 19
  137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 137 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 137 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 195 (accept_3_4 16 137 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 137 195 (Polychromatic418967fa.accept_19_15_4_5_1_11338 15 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 195 (accept_3_4 13 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 195 (Polychromatic418967fa.accept_17_11_1_8_1_7502 11 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 195 (accept_3_4 10 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 137 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 195 (accept_3_4 7 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 195 (accept_3_4 4 137 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 137 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 195 (accept_3_4 1 137 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 136 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 136 195 (accept_3_5 59 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 136 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 58 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 136 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 136 195 (accept_3_5 56 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 136 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 54 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 136 195 (accept_3_5 53 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 136 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 136 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 136 195 (accept_3_5 50 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 136 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 136 195 (accept_3_5 47 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 136 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 136 195 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 195 (accept_3_5 44 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 136 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 136 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 136 195 (accept_3_5 41 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 136 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 136 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 195 (accept_3_5 38 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 136 195
  (Polychromatic418967fa.accept_16_4_8_3_1_4206 36 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 136 195 (accept_3_5 35 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 136 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 136 195 (Polychromatic418967fa.accept_19_14_3_5_1_11347 33 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 195 (accept_3_5 32 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 136 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 136 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 30 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 136 195 (accept_3_5 29 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 136 195 (Polychromatic418967fa.accept_16_12_8_3_1_4241 28 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 136 195 (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 136 195 (accept_3_5 26 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 136 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 136 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 136 195 (accept_3_5 23 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 136 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 136 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 136 195 (accept_3_5 20 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 136 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 18 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 136 195 (accept_3_5 17 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 136 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 136 195 (Polychromatic418967fa.accept_21_15_10_6_1_11306 15 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 136 195 (accept_3_5 14 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 136 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 136 195 (accept_3_5 11 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 136 195 (Polychromatic418967fa.accept_19_10_3_5_1_11346 10 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 136 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 136 195 (accept_3_5 8 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 136 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 6 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 136 195 (accept_3_5 5 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  136 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 136 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 136 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 136 195 (accept_3_5 2 136 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 136 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 135 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 135 195 15 4 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 135 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 135 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 195 (Polychromatic418967fa.accept_16_10_7_3_1_6601 58 135
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 135 195 3 19 45 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 135 195
  (Polychromatic418967fa.accept_19_18_2_5_1_5682 56 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 55 135 195 5 11 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 135 195 3 18 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 135 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 135 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 52 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 135 195 3 17 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 50 135 195 5 10 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 135 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 49 135 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 195 3 16 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 195
  (Polychromatic418967fa.accept_16_15_7_3_1_4273 47 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 135 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 195 15 3 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 44
  135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 135 195 3 14 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 135 195 (Polychromatic418967fa.accept_16_9_7_3_1_614 41 135 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 135 195 5 8 27 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 135 195 3 13 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 135 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 195 (Polychromatic418967fa.accept_19_18_2_5_1_5682 37 135 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 195 3 12 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 135 195 5 7 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 135 195
  (Polychromatic418967fa.accept_18_16_9_15_1_4614 34 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 135 195 3 11 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 135 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 135 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 31 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 135 195 15 2 9 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 135 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 135 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 135 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 135 195 3 9 45 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 135 195
  (Polychromatic418967fa.accept_16_10_7_3_1_6601 26 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 135 195 5 5 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 135 195 3 8 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 135 195 (Polychromatic418967fa.accept_18_5_9_15_1_4695 23 135 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 135 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 195 3 7 45 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 135 195 5 4 27 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 135 195
  (Polychromatic418967fa.accept_17_2_16_8_1_3881 19 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 135 195 3 6 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 135 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 135 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 16 135
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 195 15 1 9 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 195
  (Polychromatic418967fa.accept_17_14_16_8_1_3861 14 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 135 195 (Polychromatic418967fa.accept_21_13_9_6_1_1190 13 135 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 195 3 4 45 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 135 195 5 2 27 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 135 195 3 3 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 135 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 135 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 195 (Polychromatic418967fa.accept_17_7_16_8_1_7613 7 135
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 195 3 2 45 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 135 195 5 1 27 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 135 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 135 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 195 3 1 45 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 195 (Polychromatic418967fa.accept_17_2_16_8_1_3881 2 135 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 135 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 134 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 61 134 195 (accept_3_4 61 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 134 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 134 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 134 195 (accept_3_4 58 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 134 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 134 195 (accept_3_4 55 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 134 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 134 195 (accept_3_4 52 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 134 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 134 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 134 195 (accept_3_4 49 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 134 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 134 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 134 195 (accept_3_4 46 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 134 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 134 195 (accept_3_4 43 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 134 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 134 195 (accept_3_4 40 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 134 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 39 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 134 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 38 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 134 195 (accept_3_4 37 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 134 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 36 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 134 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 134 195 (accept_3_4 34 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 134 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 134 195 (accept_3_4 31 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 134 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 134 195 (accept_3_4 28 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 134 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 134 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 26 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 134 195 (accept_3_4 25 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 134 195 (Polychromatic418967fa.accept_21_3_8_6_1_11345 24 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 134 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 134 195 (accept_3_4 22 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 134 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 134 195 (accept_3_4 19 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 134 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 134 195 (accept_3_4 16 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 134 195 (Polychromatic418967fa.accept_19_15_1_5_1_3013 15 134 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 134 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 134 195 (accept_3_4 13 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 134 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 134 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 134 195 (accept_3_4 10 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 134 195
  (Polychromatic418967fa.accept_20_8_14_15_1_6932 8 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 134 195 (accept_3_4 7 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  134 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 134 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 134 195 (accept_3_4 4 134 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 134 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 134 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 134 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 2 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 134 195 (accept_3_4 1 134 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 133 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 133 195 (accept_3_5 62 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 133 195 (Polychromatic418967fa.accept_25_11_8_20_1_11344 61 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 133 195 (Polychromatic418967fa.accept_21_18_7_6_1_3609 60 133 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 133 195 (accept_3_5 59 133 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 58
  133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 133 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 133 195 (accept_3_5 56 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 133 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 55 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 133 195 (accept_3_5 53 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 133 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 133 195
  (Polychromatic418967fa.accept_20_11_13_15_1_6931 51 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 133 195 (accept_3_5 50 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 133 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 133 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 48 133 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 195 (accept_3_5 47 133 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 195 (accept_3_5 44 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 43 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 195 (accept_3_5 41 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 39 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 195 (accept_3_5 38 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 37 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 195 (Polychromatic418967fa.accept_14_8_7_13_1_4113 36 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 195 (accept_3_5 35 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 33 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 195 (accept_3_5 32 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 195 (accept_3_5 29 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 195
  (Polychromatic418967fa.accept_10_7_3_5_1_301 27 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 195 (accept_3_5 26 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 195 (Polychromatic418967fa.accept_20_5_13_15_1_8434 25 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 195 (Polychromatic418967fa.accept_16_8_5_3_1_4297 24 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 195 (accept_3_5 23 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 21 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 195 (accept_3_5 20 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 19 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 195 (accept_3_5 17 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 195
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 195 (accept_3_5 14 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 12 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 195 (accept_3_5 11 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 195 (accept_3_5 8 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 7 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 195 (accept_3_5 5 133 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 3 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 195 (accept_3_5 2 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 133 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 132 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 63 132 195 3 21 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 132 195 (Polychromatic418967fa.accept_25_12_7_20_1_9564 62 132
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 132 195
  (Polychromatic418967fa.accept_14_5_6_13_1_3145 61 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 195 3 20 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 195 (Polychromatic418967fa.accept_18_5_6_15_1_3413 59 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 132 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 58 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 132 195 3 19 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 132 195 (Polychromatic418967fa.accept_16_8_4_3_1_3146 56 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 132 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 55 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 195 3 18 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 195 (Polychromatic418967fa.accept_10_3_2_5_1_295 53 132 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 132 195
  (Polychromatic418967fa.accept_18_16_6_15_1_3376 52 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 132 195 3 17 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 132 195 (Polychromatic418967fa.accept_20_10_12_15_1_3940 50 132 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 195
  (Polychromatic418967fa.accept_14_7_6_13_1_4111 49 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 195 3 16 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 47 132 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 195
  (Polychromatic418967fa.accept_18_10_6_15_1_3412 46 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 132 195 3 15 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 132 195 (Polychromatic418967fa.accept_16_12_4_3_1_4295 44 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 132 195
  (Polychromatic418967fa.accept_10_3_2_5_1_295 43 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 195 3 14 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 195 (Polychromatic418967fa.accept_18_5_6_15_1_3413 41 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 195
  (Polychromatic418967fa.accept_14_12_6_13_1_3173 40 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 132 195 3 13 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 132 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 38 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 195
  (Polychromatic418967fa.accept_10_7_2_5_1_298 37 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 195 3 12 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 195 (Polychromatic418967fa.accept_14_7_6_13_1_4111 35 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 132 195
  (Polychromatic418967fa.accept_18_16_6_15_1_3376 34 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 132 195 3 11 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 132 195 (Polychromatic418967fa.accept_17_15_13_8_1_7603 32 132 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 195 3 10 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 195 (Polychromatic418967fa.accept_18_11_6_15_1_5953 29 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 28 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 132 195 3 9 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 132 195 (Polychromatic418967fa.accept_14_12_6_13_1_3173 26 132 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 132 195
  (Polychromatic418967fa.accept_19_6_18_5_1_5630 25 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 195 3 8 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 132 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 23 132 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 195 (Polychromatic418967fa.accept_16_6_4_3_1_2189 22 132
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 132 195 3 7 44 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 132 195
  (Polychromatic418967fa.accept_17_3_13_8_1_11337 20 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 132 195 (Polychromatic418967fa.accept_14_5_6_13_1_3145 19 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 195 3 6 44 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 195
  (Polychromatic418967fa.accept_10_7_2_5_1_298 17 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 132 195 (Polychromatic418967fa.accept_18_16_6_15_1_3376 16 132 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 132 195 3 5 44 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 132 195
  (Polychromatic418967fa.accept_25_14_7_20_1_11343 14 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 132 195 (Polychromatic418967fa.accept_10_3_2_5_1_295 13 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 195 3 4 44 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 195
  (Polychromatic418967fa.accept_18_11_6_15_1_5953 11 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 132 195 (Polychromatic418967fa.accept_18_10_6_15_1_3412 10 132 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 132 195 3 3 44 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 132 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 8 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 132 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 195 3 2 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 195 (Polychromatic418967fa.accept_14_5_6_13_1_3145 5 132 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 195
  (Polychromatic418967fa.accept_17_4_13_8_1_3874 4 132 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 132 195 3 1 44 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 132 195 (Polychromatic418967fa.accept_19_2_18_5_1_11293 2 132 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 195 (Polychromatic418967fa.accept_16_1_4_3_1_3148 1 132 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 131 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 64 131 195 (accept_3_4 64 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 131 195 (Polychromatic418967fa.accept_18_9_5_15_1_2246 63 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 195 (accept_3_4 61 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 131 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 195
  (Polychromatic418967fa.accept_10_9_1_5_1_594 59 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 131 195 (accept_3_4 58 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 131 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 195 (accept_3_4 55 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 131 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 54 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 195 (accept_3_4 52 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 195 (Polychromatic418967fa.accept_22_7_21_19_1_11342 51 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 195 (accept_3_4 49 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 131 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 47 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 195 (accept_3_4 46 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 195 (accept_3_4 43 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 195 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 195
  (Polychromatic418967fa.accept_19_3_17_5_1_955 41 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 195 (accept_3_4 40 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 195 (accept_3_4 37 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 35 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 195 (accept_3_4 34 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 195 (accept_3_4 31 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 195 (accept_3_4 28 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 195 (Polychromatic418967fa.accept_17_10_12_8_1_2748 27 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 195 (accept_3_4 25 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 195
  (Polychromatic418967fa.accept_24_23_11_3_1_4226 23 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 131 195 (accept_3_4 22 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 131 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 131 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 195 (accept_3_4 19 131 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 195 (Polychromatic418967fa.accept_7_4_5_6_1_344
  18 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 17 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 195 (accept_3_4 16 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 195 (accept_3_4 13 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 195 (accept_3_4 10 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 195 (accept_3_4 7 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 6 131 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 195
  (Polychromatic418967fa.accept_17_5_12_8_1_6304 5 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 195 (accept_3_4 4 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 131 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 195 (accept_3_4 1 131 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66
  130 195 (Eq.refl Bool.true) (allA_succ_of_gcd 65 130 195 65 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 130 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 64 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 130 195
  (Polychromatic418967fa.accept_16_15_2_3_1_4262 63 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 130 195 (accept_3_5 62 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 130 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 130 195 5 12 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 130 195 (accept_3_5 59 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 130 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 130 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 130 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 130 195 (accept_3_5 56 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 130 195 5 11 26 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 130 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 54 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 130 195 (accept_3_5 53 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52
  130 195 13 4 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 51 130 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 130 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 195 5 10 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 130 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 130 195 (accept_3_5 47 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 130 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 130 195 5 9 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 130 195 (accept_3_5 44 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 130 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 130 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 195 (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 130
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 130 195 (accept_3_5 41 130
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 130 195 5 8 26 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 130 195 13 3 10 15 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 130 195 (accept_3_5 38 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 195
  (Polychromatic418967fa.accept_17_2_11_8_1_2726 36 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 35 130 195 5 7 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 34 130 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 130 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 130 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 195 (accept_3_5 32 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 130 195 5 6 26 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 130 195 (accept_3_5 29
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 130 195
  (Polychromatic418967fa.accept_9_1_4_6_1_5 28 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 130 195 (Polychromatic418967fa.accept_18_9_4_15_1_555 27 130 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 195 13 2 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 130 195 5 5 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 130 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 24
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 130 195 (accept_3_5 23
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 130 195
  (Polychromatic418967fa.accept_16_6_2_3_1_4223 22 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 130 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 195 5 4 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 130 195 (accept_3_5 17 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 130 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 130 195 5 3 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 130 195 (accept_3_5 14 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 130 195 13 1 10 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 12 130 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 130 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 130 195 (accept_3_5 11 130 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 195 5 2 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 195 (accept_3_5 8 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 5 130 195 5 1 26 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 4 130 195 (Polychromatic418967fa.accept_20_4_10_15_1_6919 4 130 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 130 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 195 (accept_3_5 2 130 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1
  130 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 129 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 129 195 3 22 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 129 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 129 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 64
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 129 195 3 21 43 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 129 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 61 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 129 195 3 20 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 129 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 129 195 3 19 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 129 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 55
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 129 195 3 18 43 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 129 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 53 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 129 195 3 17 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 129 195 3 16 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 129 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 47 129 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 129 195 3 15 43 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 129 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 195 3 14 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 40 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 129 195 3 13 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 129 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 129 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 37
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 129 195 3 12 43 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 129 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 35 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 129 195 3 11 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 129 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 32
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 31 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 129 195 3 10 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 129 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 29 129 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 28
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 195 3 9 43 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 25 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 129 195 3 8 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 129 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 129 195 3 7 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 129 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 129 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 195 3 6 43 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 17 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 129 195 3 5 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 129 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 13 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 195 3 4 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 195 3 3 43 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 8 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 195 3 2 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 129 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 4 129 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 195 3 1 43 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 129 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 128 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 128 195 (accept_3_4 67 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 128 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 128 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 128 195 (accept_3_4 64 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 128 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 128 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 128 195 (accept_3_4 61 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 128 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 128 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 128 195 (accept_3_4 58 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 128 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 128 195
  (Polychromatic418967fa.accept_21_14_2_6_1_11341 56 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 128 195 (accept_3_4 55 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 128 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 128 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 128 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 195 (accept_3_4 52 128 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 195
  (Polychromatic418967fa.accept_19_13_14_5_1_8545 51 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 128 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 195 (accept_3_4 49 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 128 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 128 195 (accept_3_4 46 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 128 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 128 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 44 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 195 (accept_3_4 43 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 128 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 42 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 41 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 128 195 (accept_3_4 40 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 128 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 128 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 195 (accept_3_4 37 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 128 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 195 (accept_3_4 34 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 33 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 195 (accept_3_4 31 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 195 (accept_3_4 28 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 26 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 195 (accept_3_4 25 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 128 195 (accept_3_4 22 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 128 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 128 195 (Polychromatic418967fa.accept_21_20_2_6_1_8260 20 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 195 (accept_3_4 19 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 128 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 195 (accept_3_4 16 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 195 (accept_3_4 13 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 195 (accept_3_4 10 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 195 (Polychromatic418967fa.accept_19_9_14_5_1_1890 9 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 195 (accept_3_4 7 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 128 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 195 (accept_3_4 4 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 128 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 2 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 195 (accept_3_4 1 128 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 128 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  69 127 195 (Eq.refl Bool.true) (allA_succ_of_accept 68 127 195 (accept_3_5 68 127 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 127 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 127 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 66
  127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 127 195 (accept_3_5 65
  127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 127 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 127 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 127 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 195 (accept_3_5 62 127 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 127 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 195 (Polychromatic418967fa.accept_8_4_7_3_1_144
  60 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 127 195 (accept_3_5 59
  127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 127 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 58 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 127 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 127 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 195 (accept_3_5 56 127 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 127 195 (Polychromatic418967fa.accept_16_7_15_3_1_1302 55 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 195 (accept_3_5 53 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 195 (accept_3_5 50 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 195 (accept_3_5 47 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 195 (accept_3_5 44 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 127 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 195
  (Polychromatic418967fa.accept_10_2_7_5_1_605 42 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 195 (accept_3_5 41 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 195 (accept_3_5 38 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 36 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 195 (accept_3_5 35 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 195 (accept_3_5 32 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 31 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 195 (accept_3_5 29 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 195 (Polychromatic418967fa.accept_16_11_15_3_1_1304 27 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 195 (accept_3_5 26 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 127 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 195
  (Polychromatic418967fa.accept_21_3_1_6_1_1162 24 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 195 (accept_3_5 23 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 195 (accept_3_5 20 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 195
  (Polychromatic418967fa.accept_10_8_7_5_1_602 18 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 195 (accept_3_5 17 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 195 (Polychromatic418967fa.accept_21_15_1_6_1_8258 15 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 195 (accept_3_5 14 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 127 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 195 (accept_3_5 11 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 195 (accept_3_5 8 127 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 127 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 195
  (Polychromatic418967fa.accept_22_6_17_19_1_11340 6 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 127 195 (accept_3_5 5 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 127 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 127 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 127 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 195 (accept_3_5 2 127 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 195 (Polychromatic418967fa.accept_20_1_7_15_1_1521
  1 127 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 126 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 69 126 195 3 23 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 126 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 68 126 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 126 195
  (Polychromatic418967fa.accept_17_16_7_8_1_7638 67 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 195 3 22 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 126 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 126 195 (Polychromatic418967fa.accept_10_4_6_5_1_74
  64 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 126 195 3 21 42 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 126 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 62 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 126 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 126 195 3 20 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 126 195 (Polychromatic418967fa.accept_10_9_6_5_1_1002
  59 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 126 195
  (Polychromatic418967fa.accept_11_3_5_8_1_458 58 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 126 195 3 19 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 126 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 126 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 195 (Polychromatic418967fa.accept_17_4_7_8_1_7491
  55 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 126 195 3 18 42 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 126 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 126 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 52 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 126 195 3 17 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 126 195 (Polychromatic418967fa.accept_12_2_6_3_1_331
  50 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 126 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 195 3 16 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 195 (Polychromatic418967fa.accept_11_3_5_8_1_458 47 126 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 195 (Polychromatic418967fa.accept_11_2_5_8_1_470
  46 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 126 195 3 15 42 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 126 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 44 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 126 195 (Polychromatic418967fa.accept_16_11_14_3_1_3140 43 126 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 126 195 3 14 42 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 126 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 126 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 126 195 3 13 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 126 195 (Polychromatic418967fa.accept_12_2_6_3_1_331
  38 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 195 3 12 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 126 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 195 (Polychromatic418967fa.accept_10_4_6_5_1_74
  34 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 126 195 3 11 42 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 126 195
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 195 (Polychromatic418967fa.accept_10_1_6_5_1_304 31 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 195 3 10 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 195
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 126 195 3 9 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 126 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 195 3 8 42 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 195
  (Polychromatic418967fa.accept_19_4_12_5_1_8615 23 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 195 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 195 3 7 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 195 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 195
  (Polychromatic418967fa.accept_10_9_6_5_1_1002 19 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 195 3 6 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 195 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 126
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 126 195 3 5 42 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 126 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 14 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 195 3 4 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 195 (Polychromatic418967fa.accept_10_1_6_5_1_304
  11 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 126 195 3 3 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 126 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 195 (Polychromatic418967fa.accept_19_7_12_5_1_7123 7 126
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 195 3 2 42 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 4 126 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 195 3 1 42 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 126 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 125 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 70 125 195 5 14 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 125 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 125 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 125 195 (accept_3_4 67 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 125 195 5 13 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 125 195 (accept_3_4 64 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 125 195 (Polychromatic418967fa.accept_16_15_13_3_1_4215 63 125 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 62
  125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 125 195 (accept_3_4 61
  125 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 125 195 5 12 25 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 125 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 59 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 125 195 (accept_3_4 58 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 57 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 125 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 125 195 5 11 25 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 125 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 125 195 (Polychromatic418967fa.accept_19_15_11_5_1_5713 53 125 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 195 (accept_3_4 52 125 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 125 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 125 195 5 10 25 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 125 195 (accept_3_4 49 125 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48
  125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 47 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 195 (accept_3_4 46 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45
  125 195 5 9 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  44 125 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 125 195 (accept_3_4 43 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 125 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 125 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 125 195 5 8 25 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 125 195
  (Polychromatic418967fa.accept_9_3_8_6_1_80 39 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 125 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 195 (accept_3_4 37 125 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 125 195 (Polychromatic418967fa.accept_19_17_11_5_1_7092 36 125 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 125 195 5 7 25 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 125 195 (accept_3_4 34 125 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 195 (Polychromatic418967fa.accept_12_9_5_3_1_782
  33 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 195 (accept_3_4 31 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  125 195 5 6 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 125 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 29 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 125 195 (accept_3_4 28 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 125 195 (Polychromatic418967fa.accept_18_9_17_15_1_2267 27 125 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 125 195 5 5 25 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 125 195
  (Polychromatic418967fa.accept_16_8_13_3_1_4253 24 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 125 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 125 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 195 (accept_3_4 22 125 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 125 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 125 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 125 195 5 4 25 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 125 195 (accept_3_4 19 125 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 195
  (Polychromatic418967fa.accept_16_1_13_3_1_2168 17 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 195 (accept_3_4 16 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  125 195 5 3 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 125 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 125 195 (accept_3_4 13 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 125 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 125 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 11 125 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 125 195 5 2 25 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 125 195
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 125 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 195 (accept_3_4 7 125 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 125 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 125 195 5 1 25 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 125 195 (accept_3_4 4 125 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 3 125 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 195 (accept_3_4 1 125 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 124 195 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 124 195 (accept_3_5 71 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 124 195 (Polychromatic418967fa.accept_19_13_10_5_1_11329 70 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 124 195 (Polychromatic418967fa.accept_10_9_4_5_1_616 69 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 124 195 (accept_3_5 68 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 124 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 124 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 124 195 (accept_3_5 65 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 124 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 64 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 124 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 124 195 (accept_3_5 62 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 61 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 124 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 60 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 124 195 (accept_3_5 59 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 124 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 58 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 124 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 124 195 (accept_3_5 56 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 124 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 124 195 (accept_3_5 53 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 124 195 (Polychromatic418967fa.accept_16_4_12_3_1_2180 52 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 124 195 (Polychromatic418967fa.accept_10_1_4_5_1_1031 51 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 195 (accept_3_5 50 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 124 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 124 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 124 195 (accept_3_5 47 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 124 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 46 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 124 195 (Polychromatic418967fa.accept_18_9_16_15_1_2241 45 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 195 (accept_3_5 44 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 124 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 124 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 124 195 (accept_3_5 41 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 124 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 40 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 124 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 124 195 (accept_3_5 38 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 124 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 124 195 (accept_3_5 35 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 124 195 (Polychromatic418967fa.accept_14_6_12_13_1_3180 34 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 124 195 (Polychromatic418967fa.accept_19_14_10_5_1_3073 33 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 124 195 (accept_3_5 32 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 124 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 30 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 124 195 (accept_3_5 29 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 124 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 124 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 27 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 195 (accept_3_5 26 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 124 195
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 24 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 124 195 (accept_3_5 23 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 124 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 22 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 124 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 124 195 (accept_3_5 20 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 124 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 124 195 (accept_3_5 17 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 124 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 124 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 124 195 (accept_3_5 14 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 124 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 124 195 (accept_3_5 11 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 124 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 124 195 (Polychromatic418967fa.accept_10_9_4_5_1_616 9 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 124 195 (accept_3_5 8 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 124 195
  (Polychromatic418967fa.accept_10_6_4_5_1_615 6 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 124 195 (accept_3_5 5 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  124 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 4 124 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 124 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 124 195 (accept_3_5 2 124 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 124 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 124
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 123 195 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 123 195 3 24 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 123 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 123 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 123 195
  (Polychromatic418967fa.accept_16_6_11_3_1_2198 70 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 123 195 3 23 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 123 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 123 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 195 (Polychromatic418967fa.accept_10_7_3_5_1_301
  67 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 123 195 3 22 41 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 123 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 195 (Polychromatic418967fa.accept_17_13_4_8_1_3830 64 123 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 123 195 3 21 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 123 195 (Polychromatic418967fa.accept_10_2_3_5_1_996
  62 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 61 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 123 195 3 20 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 123 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 123 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 195 (Polychromatic418967fa.accept_7_2_4_6_1_166
  58 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 123 195 3 19 41 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 123 195
  (Polychromatic418967fa.accept_16_8_11_3_1_4279 56 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 123 195 (Polychromatic418967fa.accept_16_7_11_3_1_1330 55 123 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 123 195 3 18 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 123 195 (Polychromatic418967fa.accept_19_15_9_5_1_5656
  53 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 123 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 52 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 123 195 3 17 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 123 195 (Polychromatic418967fa.accept_19_12_9_5_1_8593 50 123 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 195
  (Polychromatic418967fa.accept_11_5_2_8_1_866 49 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 123 195 3 16 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 123 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 123 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 195
  (Polychromatic418967fa.accept_16_14_11_3_1_4249 46 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 123 195 3 15 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 123 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 123 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 195
  (Polychromatic418967fa.accept_22_21_13_19_1_11339 43 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 123 195 3 14 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 123 195 (Polychromatic418967fa.accept_17_7_4_8_1_7678 41 123 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 40 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 195 3 13 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 123 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 195 (Polychromatic418967fa.accept_7_2_4_6_1_166
  37 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 195 3 12 41 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 195
  (Polychromatic418967fa.accept_17_1_4_8_1_5049 35 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 195 (Polychromatic418967fa.accept_19_15_9_5_1_5656 34 123 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 123 195 3 11 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 123 195 (Polychromatic418967fa.accept_10_2_3_5_1_996
  32 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 31 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 195 3 10 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 195 (Polychromatic418967fa.accept_17_12_4_8_1_5073 29 123 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 195
  (Polychromatic418967fa.accept_10_8_3_5_1_613 28 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 123 195 3 9 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 123 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 123 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 195 (Polychromatic418967fa.accept_20_5_3_15_1_6909 25 123
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 195 3 8 41 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 195 (Polychromatic418967fa.accept_10_2_3_5_1_996 22 123 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 123 195 3 7 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 123 195 (Polychromatic418967fa.accept_19_1_9_5_1_9939
  20 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 123 195 3 6 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 123 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 123 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 123 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 123 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 195 3 5 41 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 195
  (Polychromatic418967fa.accept_16_14_11_3_1_4249 14 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 123 195 (Polychromatic418967fa.accept_17_13_4_8_1_3830 13 123 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 123 195 3 4 41 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 123 195
  (Polychromatic418967fa.accept_21_11_18_6_1_3521 11 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 123 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 10 123 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 195 3 3 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 195 (Polychromatic418967fa.accept_10_8_3_5_1_613 8
  123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 195
  (Polychromatic418967fa.accept_10_7_3_5_1_301 7 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 123 195 3 2 41 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 123 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 123 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 195 (Polychromatic418967fa.accept_19_4_9_5_1_8572 4 123 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 123 195 3 1 41 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 123 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 123 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 123 195 (Polychromatic418967fa.accept_17_1_4_8_1_5049 1 123 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 123
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 122 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 122 195 (accept_3_4 73 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 122 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 122 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 122 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 122 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 122 195 (accept_3_4 70 122 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 122 195
  (Polychromatic418967fa.accept_10_8_2_5_1_596 68 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 122 195 (accept_3_4 67 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 122 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 122 195 (accept_3_4 64 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 122 195 (Polychromatic418967fa.accept_10_3_2_5_1_295 63 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 122 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 62 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 122 195 (accept_3_4 61 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 122 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 122 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 195 (accept_3_4 58 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 56 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 195 (accept_3_4 55 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 195 (accept_3_4 52 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 195
  (Polychromatic418967fa.accept_19_12_8_5_1_8538 50 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 195 (accept_3_4 49 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 195 (accept_3_4 46 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 195 (accept_3_4 43 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 195 (accept_3_4 40 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 38 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 195 (accept_3_4 37 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 195 (Polychromatic418967fa.accept_21_15_17_6_1_6661 36 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 122 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 195 (accept_3_4 34 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 195 (accept_3_4 31 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 195 (accept_3_4 28 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 195 (Polychromatic418967fa.accept_10_7_2_5_1_298 27 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 26 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 195 (accept_3_4 25 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 195 (Polychromatic418967fa.accept_20_4_2_15_1_6904 24 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 195 (accept_3_4 22 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 195 (accept_3_4 19 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 195 (accept_3_4 16 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 195 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 195
  (Polychromatic418967fa.accept_19_14_8_5_1_8606 14 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 195 (accept_3_4 13 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 195 (accept_3_4 10 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 195 (accept_3_4 7 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 195 (accept_3_4 4 122 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 122 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 195 (accept_3_4 1 122 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 121 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 74 121 195 (accept_3_5 74 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 121 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 73 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 121 195 (Polychromatic418967fa.accept_21_9_16_6_1_5134 72 121
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 121 195 (accept_3_5 71 121
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 121 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 121 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 195 (accept_3_5 68 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 121 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 67 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 121 195 (accept_3_5 65
  121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 121 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 121 195 (Polychromatic418967fa.accept_19_6_7_5_1_256 63 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 195 (accept_3_5 62 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 121 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 195 (Polychromatic418967fa.accept_7_4_2_6_1_337
  60 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 195 (accept_3_5 59
  121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 121 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 195 (accept_3_5 56 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 121 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54
  121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 195 (accept_3_5 53
  121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 52 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 51 121 195 (Polychromatic418967fa.accept_19_13_7_5_1_5712 51 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 195 (accept_3_5 50 121 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 121 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 49 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 195 (accept_3_5 47 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 195 (accept_3_5 44 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 43 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 195 (accept_3_5 41 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 195 (accept_3_5 38 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 36 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 195 (accept_3_5 35 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 195 (Polychromatic418967fa.accept_12_9_1_3_1_350 33 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 195 (accept_3_5 32 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 121 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 121 195 (accept_3_5 29 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 121 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 121 195 (Polychromatic418967fa.accept_17_10_2_8_1_6295 27 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 195 (accept_3_5 26 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 25 121 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 24 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 195 (accept_3_5 23 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 195 (accept_3_5 20 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 195 (accept_3_5 17 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 195 (accept_3_5 14 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 195 (Polychromatic418967fa.accept_19_13_7_5_1_5712 13 121 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 12 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 195 (accept_3_5 11 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 9 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 195 (accept_3_5 8 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 195 (accept_3_5 5 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 195 (accept_3_5 2 121 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 1 121 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 120 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 120 195 15 5 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 120 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 74 120 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 120 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 73
  120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 120 195 3 24 40 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 120 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 71 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 120 195 5 14 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 120 195 3 23 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 120 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 120 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 120 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 67 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 195 3 22 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 120 195 5 13 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 120 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 120 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 120 195 3 21 40 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 120 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 62 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 120 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 61 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 120 195 15 4 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 120 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 59
  120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 58 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 120 195 3 19 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 120 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 56 120 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 120 195 5 11 24 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 120 195 3 18 40 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 195
  (Polychromatic418967fa.accept_9_8_3_6_1_533 53 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 120 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 52 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 120 195 3 17 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 195 5 10 24 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 49 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 195 3 16 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 120 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 46
  120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 120 195 15 3 8 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 120 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 120 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 43 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 120 195 3 14 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 120 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 41
  120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 195 5 8 24 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 195 3 13 40 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 120 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 120 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 37 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 120 195 3 12 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 120 195 5 7 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 120 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 34
  120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 120 195 3 11 40 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 120 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 120 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 31 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 120 195 15 2 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 120 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 29
  120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 120 195 3 9 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 120 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 120 195 5 5 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 120 195 3 8 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 23
  120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 120 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 22 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 120 195 3 7 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 120 195 5 4 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 120 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 19 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 195 3 6 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 16 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 120 195 15 1 8 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 120 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 120 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 195 3 4 40 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 120 195 5 2 24 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 120 195 3 3 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 120 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 120 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 120 195 3 2 40 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 120 195 5 1 24 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 120 195
  (Polychromatic418967fa.accept_9_4_3_6_1_532 4 120 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 120 195 3 1 40 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 120 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 120 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 120 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 120 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 119 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 119 195 (accept_3_4 76 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 119 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 119 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 119 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 119 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 119 195 (accept_3_4 73 119 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 119 195
  (Polychromatic418967fa.accept_21_9_14_6_1_11308 72 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 119 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 195 (accept_3_4 70 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 195 (accept_3_4 67 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 119 195 (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 195 (accept_3_4 64 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 195 (Polychromatic418967fa.accept_16_15_7_3_1_4273 63 119
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 195 (accept_3_4 61 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 60 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 195 (accept_3_4 58 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 195 (accept_3_4 55 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 54 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 53 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 195 (accept_3_4 52 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 51 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 195 (accept_3_4 49 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 195 (Polychromatic418967fa.accept_16_15_7_3_1_4273 47 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 195 (accept_3_4 46 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 119
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 195 (accept_3_4 43 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 195 (Polychromatic418967fa.accept_16_10_7_3_1_6601 42 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 195 (accept_3_4 40 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 39 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 195 (accept_3_4 37 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 36 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 195 (accept_3_4 34 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 33 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 195 (accept_3_4 31 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 30 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 29 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 195 (accept_3_4 28 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 195 (Polychromatic418967fa.accept_16_11_7_3_1_3163 27 119
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 195 (accept_3_4 25 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 195 (Polychromatic418967fa.accept_10_4_9_5_1_84 24 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 23 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 195 (accept_3_4 22 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 195 (accept_3_4 19 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 195 (Polychromatic418967fa.accept_21_18_14_6_1_8278 18 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 119 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 195 (accept_3_4 16 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 195 (Polychromatic418967fa.accept_14_1_7_13_1_333 15 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 195 (accept_3_4 13 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 12 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 11 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 195 (accept_3_4 10 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 195 (accept_3_4 7 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 195 (Polychromatic418967fa.accept_10_6_9_5_1_1046 6 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 195 (accept_3_4 4 119 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 119 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 195 (accept_3_4 1 119 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 118 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 118 195 (accept_3_5 77 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 118 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 118 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 118 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 75 118 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 118 195 (accept_3_5 74 118 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 118 195
  (Polychromatic418967fa.accept_10_2_8_5_1_587 72 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 118 195 (accept_3_5 71 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 118 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 70 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 118 195 (accept_3_5 68 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 118 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 118 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 66 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 118 195 (accept_3_5 65 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 195 (Polychromatic418967fa.accept_22_20_8_19_1_9748 64 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 63 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 195 (accept_3_5 62 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 195
  (Polychromatic418967fa.accept_17_9_16_8_1_2721 60 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 195 (accept_3_5 59 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 195 (accept_3_5 56 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 195 (accept_3_5 53 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 52 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 195 (Polychromatic418967fa.accept_21_9_13_6_1_2285 51 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 195 (accept_3_5 50 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 195 (accept_3_5 47 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 195 (Polychromatic418967fa.accept_19_8_4_5_1_8569 46 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 195 (accept_3_5 44 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 195
  (Polychromatic418967fa.accept_10_2_8_5_1_587 42 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 195 (accept_3_5 41 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 40 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 195 (accept_3_5 38 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 195
  (Polychromatic418967fa.accept_16_4_6_3_1_1311 36 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 195 (accept_3_5 35 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 34 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 195 (accept_3_5 32 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 30 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 195 (accept_3_5 29 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 195 (Polychromatic418967fa.accept_19_9_4_5_1_3019 28 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 27 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 195 (accept_3_5 26 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 195
  (Polychromatic418967fa.accept_17_7_16_8_1_7613 24 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 195 (accept_3_5 23 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 22 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 195 (accept_3_5 20 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 195 (accept_3_5 17 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 195 (Polychromatic418967fa.accept_19_15_4_5_1_11338 15 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 195 (accept_3_5 14 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 195 (accept_3_5 11 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 195 (Polychromatic418967fa.accept_20_10_18_15_1_5359 10 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 195 (accept_3_5 8 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 118 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 195 (accept_3_5 5 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 4 118 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 3 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 195 (accept_3_5 2 118 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 117 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 117 195 39 2 3 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 117 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 117 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 117 195 (Polychromatic418967fa.accept_14_6_5_13_1_367
  76 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 117 195 3 25 39 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 117 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 117 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 73 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 117 195 3 24 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 117 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 71
  117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 117 195 3 23 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 117 195 (Polychromatic418967fa.accept_10_8_7_5_1_602 68 117 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 195 (Polychromatic418967fa.accept_7_4_5_6_1_344
  67 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 117 195 3 22 39 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 65 117 195 13 5 9 15
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 117 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 64 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 195 3 21 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 117 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 195 (Polychromatic418967fa.accept_12_1_9_3_1_370
  61 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 195 3 20 39 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 195
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 59 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 117 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 117 195 3 19 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 117 195 (Polychromatic418967fa.accept_16_8_5_3_1_4297
  56 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 55 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 117 195 3 18 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 117 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 117 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 117 195 13 4 9 15 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 117 195 3 17 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 117 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 117 195 3 16 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 117 195 (Polychromatic418967fa.accept_12_11_9_3_1_792
  47 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 195 3 15 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 117 195 (Polychromatic418967fa.accept_17_10_15_8_1_6324 44 117 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 43 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 117 195 3 14 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 117 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 41 117 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 195 (Polychromatic418967fa.accept_16_8_5_3_1_4297
  40 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 195 39 1 3 5 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 37 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 117 195 3 12 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 117 195 (Polychromatic418967fa.accept_12_11_9_3_1_792
  35 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 195 3 11 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 117 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 195 (Polychromatic418967fa.accept_12_7_9_3_1_767
  31 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 195 3 10 39 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 195 (Polychromatic418967fa.accept_10_8_7_5_1_602 28 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 195 3 9 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 117 195 13 2 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 117 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 25
  117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 195 3 8 39 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 195
  (Polychromatic418967fa.accept_10_3_7_5_1_288 23 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 195 3 7 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 195 (Polychromatic418967fa.accept_14_6_5_13_1_367
  20 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 195 3 6 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 195 (Polychromatic418967fa.accept_18_16_9_15_1_4614 16 117
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 195 3 5 39 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 117 195 13 1 9 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 117 195 3 4 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 117 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 195 3 3 39 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 195 3 2 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 5 117 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 4 117 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 195 3 1 39 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 117 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 116 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 116 195 (accept_3_4 79 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 116 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 78 116 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 116 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 116 195 (accept_3_4 76 116 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 116 195 (Polychromatic418967fa.accept_7_5_4_6_1_167
  75 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 116 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 74 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 116 195 (accept_3_4 73 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 116 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 116 195 (accept_3_4 70 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 116 195 (Polychromatic418967fa.accept_10_9_6_5_1_1002 69 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 116 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 116 195 (accept_3_4 67 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 116 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 116 195 (accept_3_4 64 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 116 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 63 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 116 195
  (Polychromatic418967fa.accept_17_11_14_8_1_2729 62 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 116 195 (accept_3_4 61 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 116 195 (Polychromatic418967fa.accept_16_12_4_3_1_4295 60 116 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 116 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 116 195 (accept_3_4 58 116 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 116 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 57
  116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 116 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 56 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 116 195 (accept_3_4 55 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 116 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 195 (accept_3_4 52 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 116 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 50 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 116 195 (accept_3_4 49 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 116 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 195 (accept_3_4 46 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 116 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 116 195 (accept_3_4 43 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 116 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 195 (accept_3_4 40 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 39 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 195 (accept_3_4 37 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 195 (Polychromatic418967fa.accept_11_3_6_8_1_1924 36 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 195 (accept_3_4 34 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 32 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 195 (accept_3_4 31 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 195 (accept_3_4 28 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 195 (Polychromatic418967fa.accept_19_8_2_5_1_5678 27 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 195 (accept_3_4 25 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 195 (accept_3_4 22 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 195
  (Polychromatic418967fa.accept_9_2_8_6_1_79 20 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 195 (accept_3_4 19 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 195 (accept_3_4 16 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 15 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 195
  (Polychromatic418967fa.accept_9_5_8_6_1_281 14 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 195 (accept_3_4 13 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 195 (accept_3_4 10 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 195
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 8 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 195 (accept_3_4 7 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 6 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 195 (accept_3_4 4 116 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 116 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 195 (accept_3_4 1 116 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 81 115 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 80 115 195 5 16 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 115 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 115 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 115 195
  (Polychromatic418967fa.accept_21_15_10_6_1_11306 78 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 115 195 (accept_3_5 77 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 115 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 115 195 5 15 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 115 195 (accept_3_5 74 115 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 73 115 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 115 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 115 195 (accept_3_5 71 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  115 195 5 14 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 115 195 (Polychromatic418967fa.accept_11_3_5_8_1_458 69 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 115 195 (accept_3_5 68 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 115 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 67 115 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 115 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 66
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 115 195 5 13 23 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 115 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 115 195 (Polychromatic418967fa.accept_19_6_1_5_1_5719 63 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 115 195 (accept_3_5 62 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 115 195 (Polychromatic418967fa.accept_19_4_1_5_1_9933 61 115 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 115 195 5 12 23 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 115 195 (accept_3_5 59 115 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 58
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 57 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 195 (accept_3_5 56 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55
  115 195 5 11 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 54 115 195 (Polychromatic418967fa.accept_17_3_13_8_1_11337 54 115 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 195 (accept_3_5 53 115 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 115 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 115 195 5 10 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 115 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 49 115 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 115 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 48
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 195 (accept_3_5 47
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 46 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 115 195 5 9 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 115 195 (accept_3_5 44 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 195 (Polychromatic418967fa.accept_25_18_15_20_1_7727 43 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 115 195 (Polychromatic418967fa.accept_19_4_1_5_1_9933 42 115 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 195 (accept_3_5 41 115 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 115 195 5 8 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 115 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 39
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 115 195 (accept_3_5 38
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 115 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 115 195 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 115 195 5 7 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 115 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 195
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 195 (accept_3_5 32 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 31 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 115 195 5 6 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 115 195 (accept_3_5 29 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 195 (Polychromatic418967fa.accept_25_2_15_20_1_11336 27
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 195 (accept_3_5 26
  115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 115 195 5 5 23 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 115 195
  (Polychromatic418967fa.accept_11_2_5_8_1_470 24 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 115 195 (accept_3_5 23 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 115 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 115 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 21 115 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 115 195 5 4 23 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 115 195
  (Polychromatic418967fa.accept_9_1_7_6_1_75 19 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 115 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 195 (accept_3_5 17 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 115 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 115 195 5 3 23 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 115 195 (accept_3_5 14 115 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 115 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 13 115 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 115 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 12 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 115 195 (accept_3_5 11 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  115 195 5 2 23 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 115 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 115 195 (accept_3_5 8 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 115 195 (Polychromatic418967fa.accept_24_7_19_3_1_11335 7 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 115 195 (Polychromatic418967fa.accept_19_6_1_5_1_5719 6 115 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 115 195 5 1 23 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 115 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 115 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 115 195 (accept_3_5 2 115 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 115 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 1 115 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 115
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 114 195 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 114 195 3 27 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 114 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 80 114 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 114 195
  (Polychromatic418967fa.accept_10_9_4_5_1_616 79 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 114 195 3 26 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 114 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 114 195 (Polychromatic418967fa.accept_10_6_4_5_1_615
  76 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 114 195 3 25 38 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 114 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 114 195 3 24 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 114 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 71
  114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 114 195
  (Polychromatic418967fa.accept_12_10_6_3_1_786 70 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 114 195 3 23 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 114 195 (Polychromatic418967fa.accept_12_8_6_3_1_366 68 114 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 195 (Polychromatic418967fa.accept_7_4_2_6_1_337
  67 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 114 195 3 22 38 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 114 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 114 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 114 195 3 21 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 114 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371
  62 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 114 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 114 195 3 20 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 114 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 114 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 195 (Polychromatic418967fa.accept_12_10_6_3_1_786
  58 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 114 195 3 19 38 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 114 195
  (Polychromatic418967fa.accept_10_6_4_5_1_615 56 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 114 195 (Polychromatic418967fa.accept_17_4_12_8_1_3833 55 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 114 195 3 18 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53
  114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 114 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 52 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 114 195 3 17 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 114 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 114 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 195 3 16 38 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 195
  (Polychromatic418967fa.accept_16_15_2_3_1_4262 47 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 114 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 114 195 3 15 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 114 195 (Polychromatic418967fa.accept_12_8_6_3_1_366
  44 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 114 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 43 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 114 195 3 14 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 114 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371
  40 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 114 195 3 13 38 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 114 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 195 3 12 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 195
  (Polychromatic418967fa.accept_18_17_6_15_1_8704 35 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 114 195 (Polychromatic418967fa.accept_11_1_4_8_1_1918 34 114 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 114 195 3 11 38 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 114 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 114 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 31 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 195 3 10 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 195
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 114 195 3 9 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 114 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 26 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 195 3 8 38 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 195
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 114 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 114 195 3 7 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 114 195 (Polychromatic418967fa.accept_12_8_6_3_1_366
  20 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 195
  (Polychromatic418967fa.accept_10_9_4_5_1_616 19 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 114 195 3 6 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 114 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 16 114
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 195 3 5 38 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 195
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 114 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 195 3 4 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 11
  114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 10 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 114 195 3 3 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 114 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 114 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 7 114 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 195 3 2 38 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 114 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 4 114 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 114 195 3 1 38 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 114 195 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 114 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 114 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 113
  195 (Eq.refl Bool.true) (allA_succ_of_accept 82 113 195 (accept_3_4 82 113 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 113 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 81 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 113 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 113 195 (accept_3_4 79 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 113 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 113 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 77 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 195 (accept_3_4 76 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 113 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 113 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 113 195 (accept_3_4 73 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 113 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 113 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 71 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 195 (accept_3_4 70 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 69 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 113 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 113 195 (accept_3_4 67 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 113 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 113 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 113 195 (accept_3_4 64 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 113 195 (Polychromatic418967fa.accept_14_7_1_13_1_357 63 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 113 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 113 195 (accept_3_4 61 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 113 195 (Polychromatic418967fa.accept_11_5_3_8_1_454 60 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 113 195 (Polychromatic418967fa.accept_19_2_18_5_1_11293 59 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 113 195 (accept_3_4 58 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 113 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 113 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 113 195 (accept_3_4 55 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 113 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 113 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 53 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 113 195 (accept_3_4 52 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 113 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 113 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 113 195 (accept_3_4 49 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 113 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 113 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 113 195 (accept_3_4 46 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 113 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 113 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 113 195 (accept_3_4 43 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 113 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 113 195 (Polychromatic418967fa.accept_25_16_13_20_1_11334 41 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 113 195 (accept_3_4 40 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 113 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 39 113 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 113 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 113 195 (accept_3_4 37 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 113 195 (Polychromatic418967fa.accept_16_4_1_3_1_6581 36 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 113 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 35 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 113 195 (accept_3_4 34 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 113 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 113 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 113 195 (accept_3_4 31 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 113 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 113 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 29 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 113 195 (accept_3_4 28 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 113 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 113 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 113 195 (accept_3_4 25 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 113 195 (Polychromatic418967fa.accept_18_6_5_15_1_7292 24 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 113 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 113 195 (accept_3_4 22 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 113 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 21 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 113 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 113 195 (accept_3_4 19 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 113 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 113 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 17 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 113 195 (accept_3_4 16 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 113 195 (Polychromatic418967fa.accept_21_15_8_6_1_5106 15 113 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 113 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 113 195 (accept_3_4 13 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 113 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 113 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 11 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 113 195 (accept_3_4 10 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 113 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 113 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 113 195 (accept_3_4 7 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  113 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 113 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 113 195 (accept_3_4 4 113 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 113 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 113 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 113 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 113 195 (accept_3_4 1 113 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 113
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 112 195 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 112 195 (accept_3_5 83 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 112 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 82 112 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 112 195 (Polychromatic418967fa.accept_18_9_4_15_1_555 81 112
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 112 195 (accept_3_5 80 112
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 112 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 79 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 112 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 78 112 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 112 195 (accept_3_5 77 112 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 112 195 (Polychromatic418967fa.accept_21_13_7_6_1_3656 76 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 112 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 75 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 112 195 (accept_3_5 74 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 112 195 (Polychromatic418967fa.accept_19_15_17_5_1_3052 72 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 112 195 (accept_3_5 71 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 70 112 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 195
  (Polychromatic418967fa.accept_19_12_17_5_1_5702 69 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 112 195 (accept_3_5 68 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 112 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 112 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 66 112 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 195 (accept_3_5 65 112 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 64
  112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 195
  (Polychromatic418967fa.accept_10_3_2_5_1_295 63 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 195 (accept_3_5 62 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 195 (accept_3_5 59 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 58 112
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 57 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 195 (accept_3_5 56 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 195 (accept_3_5 53 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 52 112 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 195
  (Polychromatic418967fa.accept_21_9_7_6_1_8298 51 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 195 (accept_3_5 50 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 48 112 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 195 (accept_3_5 47 112 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 46 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 195
  (Polychromatic418967fa.accept_18_9_4_15_1_555 45 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 195 (accept_3_5 44 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 42 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 195 (accept_3_5 41 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 195 (Polychromatic418967fa.accept_19_2_17_5_1_5643 40 112
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 39 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 112 195 (accept_3_5 38 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 112 195 (Polychromatic418967fa.accept_17_2_10_8_1_7691 36 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 195 (accept_3_5 35 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 34 112 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 112 195
  (Polychromatic418967fa.accept_10_3_2_5_1_295 33 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 112 195 (accept_3_5 32 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 112 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 30 112 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 195 (accept_3_5 29 112 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 28 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 112 195
  (Polychromatic418967fa.accept_10_7_2_5_1_298 27 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 112 195 (accept_3_5 26 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 112 195 (Polychromatic418967fa.accept_18_6_4_15_1_2276 24 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 195 (accept_3_5 23 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 195 (Polychromatic418967fa.accept_19_3_17_5_1_955 22 112
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 112 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 21 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 112 195 (accept_3_5 20 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 112 195 (Polychromatic418967fa.accept_10_8_2_5_1_596 18 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 195 (accept_3_5 17 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 16 112 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 112 195
  (Polychromatic418967fa.accept_17_15_10_8_1_1708 15 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 112 195 (accept_3_5 14 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 12 112 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 195 (accept_3_5 11 112 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 10
  112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 112 195
  (Polychromatic418967fa.accept_18_9_4_15_1_555 9 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 112 195 (accept_3_5 8 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 112 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 112 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 195 (accept_3_5 5 112 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 195 (Polychromatic418967fa.accept_21_4_7_6_1_3605 4 112 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 112 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 3 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 112 195 (accept_3_5 2 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  112 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 112 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 85 111 195 (Eq.refl Bool.true) (allA_succ_of_gcd 84 111 195 3 28 37 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 83 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 82 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 111 195 3 27 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 111 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 80
  111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 79 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 111 195 3 26 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 111 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 77 111 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 195 (Polychromatic418967fa.accept_8_4_7_3_1_144
  76 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 111 195 3 25 37 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 74 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 73 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 111 195 3 24 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 111 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 71
  111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 70 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 111 195 3 23 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 111 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 68 111 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 195 (Polychromatic418967fa.accept_9_4_3_6_1_532
  67 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 111 195 3 22 37 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 65 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 64 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 111 195 3 21 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 111 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 62
  111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 61 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 111 195 3 20 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 111 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 59 111 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 195 (Polychromatic418967fa.accept_9_4_3_6_1_532
  58 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 111 195 3 19 37 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 56 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 55 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 111 195 3 18 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 111 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 53
  111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 52 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 111 195 3 17 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 111 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 50 111 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 195 (Polychromatic418967fa.accept_9_4_3_6_1_532
  49 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 111 195 3 16 37 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 47 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 46 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 111 195 3 15 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 111 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 44
  111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 43 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 111 195 3 14 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 111 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 41 111 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 111 195 (Polychromatic418967fa.accept_9_4_3_6_1_532
  40 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 195 3 13 37 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 38 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 37 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 195 3 12 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 35
  111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 34 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 195 3 11 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 32 111 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 195 (Polychromatic418967fa.accept_9_4_3_6_1_532
  31 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 195 3 10 37 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 29 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 28 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 195 3 9 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 26
  111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 25 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 111 195 3 8 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 111 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 23 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 111 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 195 3 7 37 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 20 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 19 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 195 3 6 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 17
  111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 16 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 195 3 5 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 14 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 13 111 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 111 195 3 4 37 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 11 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 10 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 195 3 3 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 111 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 195
  (Polychromatic418967fa.accept_9_7_3_6_1_270 7 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 111 195 3 2 37 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 111 195 (Polychromatic418967fa.accept_9_5_3_6_1_269 5 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 195 (Polychromatic418967fa.accept_8_4_7_3_1_144 4 111 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 195 3 1 37 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 195
  (Polychromatic418967fa.accept_9_2_3_6_1_88 2 111 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 111 195 (Polychromatic418967fa.accept_9_1_3_6_1_70 1 111 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 111
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 110 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 85 110 195 5 17 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 110 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 110 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 110 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 110 195 (accept_3_4 82 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 110 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 110 195 5 16 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 110 195 (accept_3_4 79 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 110 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 110 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 110 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 110 195 (accept_3_4 76 110 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 110 195 5 15 22 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 110 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 74 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 110 195 (accept_3_4 73 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 110 195 (Polychromatic418967fa.accept_20_12_10_15_1_9869 72 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 110 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 110 195 5 14 22 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 110 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 69 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 110 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 68 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 110 195 (accept_3_4 67 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 110 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 66 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 65 110 195 5 13 22 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 64 110 195 (accept_3_4 64 110 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 110 195 (Polychromatic418967fa.accept_19_6_15_5_1_5697 63 110
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 62 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 195 (accept_3_4 61 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60
  110 195 5 12 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 59 110 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 195 (accept_3_4 58 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 110 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 195
  (Polychromatic418967fa.accept_20_16_10_15_1_5368 56 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 55 110 195 5 11 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 54 110 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 110 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 110 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 110 195 (accept_3_4 52 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 110 195 (Polychromatic418967fa.accept_20_11_10_15_1_11318 51 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 50 110 195 5 10 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 110 195 (accept_3_4 49 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 110 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 110 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47
  110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 195 (accept_3_4 46
  110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 110 195 5 9 22 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 110 195
  (Polychromatic418967fa.accept_9_8_2_6_1_875 44 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 195 (accept_3_4 43 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 42 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 195 5 8 22 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 110 195 (Polychromatic418967fa.accept_20_18_10_15_1_3937 38 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 110 195 (accept_3_4 37 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 110 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 110 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 110 195 5 7 22 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 110 195 (accept_3_4 34 110 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33
  110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 195 (accept_3_4 31 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  110 195 5 6 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  29 110 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 110 195 (accept_3_4 28 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 110 195 (Polychromatic418967fa.accept_16_11_14_3_1_3140 27 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 195 (Polychromatic418967fa.accept_9_8_2_6_1_875
  26 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 110 195 5 5 22 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 24 110 195
  (Polychromatic418967fa.accept_20_4_10_15_1_6919 24 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 195 (accept_3_4 22 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 110 195 5 4 22 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 110 195 (accept_3_4 19 110 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 110 195 (Polychromatic418967fa.accept_7_4_5_6_1_344
  18 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 110 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 110 195 (accept_3_4 16 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15
  110 195 5 3 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  14 110 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 14 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 110 195 (accept_3_4 13 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 110 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 110 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 110 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 110 195 5 2 22 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 110 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 110 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 110 195 (accept_3_4 7 110 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 110 195 (Polychromatic418967fa.accept_12_6_2_3_1_354 6 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 110 195 5 1 22 39 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 110 195 (accept_3_4 4 110 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 110 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 195
  (Polychromatic418967fa.accept_20_2_10_15_1_3953 2 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 195 (accept_3_4 1 110 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 109 195
  (Eq.refl Bool.true) (allA_succ_of_accept 86 109 195 (accept_3_5 86 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 109 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 85 109 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 109 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 84 109 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 109 195 (accept_3_5 83 109 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 109 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 82
  109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 195
  (Polychromatic418967fa.accept_10_1_9_5_1_83 81 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 80 109 195 (accept_3_5 80 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  79 109 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 79 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 78 109 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 109 195 (accept_3_5 77 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 109 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 109 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 109 195 (accept_3_5 74 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  73 109 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 73 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 109 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 195 (accept_3_5 71 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 109 195
  (Polychromatic418967fa.accept_12_9_1_3_1_350 69 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 109 195 (accept_3_5 68 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 109 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 67 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 109 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 195 (accept_3_5 65 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 109 195
  (Polychromatic418967fa.accept_16_15_13_3_1_4215 63 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 109 195 (accept_3_5 62 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 109 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 61 109 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 195 (Polychromatic418967fa.accept_19_3_14_5_1_8597 60 109
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 195 (accept_3_5 59 109
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 109 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 57 109 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 195 (accept_3_5 56 109 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 109 195 (Polychromatic418967fa.accept_17_4_7_8_1_7491 55 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 195 (accept_3_5 53 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 195 (accept_3_5 50 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 49 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 48 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 195 (accept_3_5 47 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 195 (accept_3_5 44 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 43 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 195 (accept_3_5 41 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 39 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 195 (accept_3_5 38 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 37 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 195
  (Polychromatic418967fa.accept_10_6_9_5_1_1046 36 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 195 (accept_3_5 35 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 195 (accept_3_5 32 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 195 (accept_3_5 29 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 195 (Polychromatic418967fa.accept_19_8_14_5_1_9919 27 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 195 (accept_3_5 26 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 25 109 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 24 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 195 (accept_3_5 23 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 195 (accept_3_5 20 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 19 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 195 (accept_3_5 17 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 195 (Polychromatic418967fa.accept_16_15_13_3_1_4215 15 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 195 (accept_3_5 14 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 13 109 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 12 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 195 (accept_3_5 11 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 195 (accept_3_5 8 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 7 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 195 (accept_3_5 5 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 195 (accept_3_5 2 109 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 195 (Polychromatic418967fa.accept_10_1_9_5_1_83 1 109 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 108 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 108 195 3 29 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 108 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 108 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 108 195
  (Polychromatic418967fa.accept_19_9_13_5_1_4351 85 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 108 195 3 28 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 108 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 83 108 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 108 195 (Polychromatic418967fa.accept_10_2_8_5_1_587
  82 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 108 195 3 27 36 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 108 195
  (Polychromatic418967fa.accept_25_5_8_20_1_11333 80 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 108 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 79 108 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 108 195 3 26 36 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 108 195
  (Polychromatic418967fa.accept_10_7_8_5_1_1008 77 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 108 195 (Polychromatic418967fa.accept_11_10_9_8_1_1974 76 108 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 108 195 3 25 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 108 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 74
  108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 195
  (Polychromatic418967fa.accept_10_3_8_5_1_606 73 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 195 3 24 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 108 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 71 108 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 195
  (Polychromatic418967fa.accept_20_10_8_15_1_11332 70 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 108 195 3 23 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 108 195 (Polychromatic418967fa.accept_16_4_12_3_1_2180 68 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 195
  (Polychromatic418967fa.accept_7_4_3_6_1_340 67 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 195 3 22 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 108 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 108 195
  (Polychromatic418967fa.accept_19_7_13_5_1_7125 64 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 108 195 3 21 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 108 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 62 108 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 195
  (Polychromatic418967fa.accept_21_19_3_6_1_2281 61 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 195 3 20 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 195 (Polychromatic418967fa.accept_14_3_10_13_1_339 59 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 58 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 108 195 3 19 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 108 195 (Polychromatic418967fa.accept_16_8_12_3_1_4194 56 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 108 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 55 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 195 3 18 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 108 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 108 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 195 (Polychromatic418967fa.accept_10_2_8_5_1_587
  52 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 108 195 3 17 36 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 108 195
  (Polychromatic418967fa.accept_19_12_13_5_1_11331 50 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 108 195 (Polychromatic418967fa.accept_17_15_6_8_1_6343 49 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 108 195 3 16 36 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 108 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 47 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 108 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 46 108 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 108 195 3 15 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 108 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 44
  108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 108 195
  (Polychromatic418967fa.accept_10_3_8_5_1_606 43 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 108 195 3 14 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 108 195 (Polychromatic418967fa.accept_16_9_12_3_1_3138 41 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 195
  (Polychromatic418967fa.accept_16_8_12_3_1_4194 40 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 108 195 3 13 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 108 195 (Polychromatic418967fa.accept_25_13_8_20_1_11330 38 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 37 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 108 195 3 12 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 108 195 (Polychromatic418967fa.accept_21_14_3_6_1_8231 35 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 108 195
  (Polychromatic418967fa.accept_20_14_8_15_1_8432 34 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 108 195 3 11 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 108 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 195
  (Polychromatic418967fa.accept_8_7_4_3_1_156 31 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 195 3 10 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 195 (Polychromatic418967fa.accept_19_10_13_5_1_3091 29 108 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 195
  (Polychromatic418967fa.accept_19_9_13_5_1_4351 28 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 108 195 3 9 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 108 195 (Polychromatic418967fa.accept_16_10_12_3_1_4252 26 108 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 195 (Polychromatic418967fa.accept_7_4_3_6_1_340
  25 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 108 195 3 8 36 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 108 195
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 108 195 (Polychromatic418967fa.accept_10_2_8_5_1_587 22 108 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 195 3 7 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 195 (Polychromatic418967fa.accept_16_4_12_3_1_2180
  20 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 108 195
  (Polychromatic418967fa.accept_21_19_3_6_1_2281 19 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 108 195 3 6 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 108 195 (Polychromatic418967fa.accept_10_7_8_5_1_1008 17 108 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 108 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 16 108 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 195 3 5 36 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 195
  (Polychromatic418967fa.accept_17_14_6_8_1_7688 14 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 108 195 (Polychromatic418967fa.accept_10_3_8_5_1_606 13 108 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 195 3 4 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 11
  108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 108 195
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 10 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 108 195 3 3 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 108 195 (Polychromatic418967fa.accept_16_8_12_3_1_4194 8 108 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 195 (Polychromatic418967fa.accept_8_7_4_3_1_156 7 108 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 195 3 2 36 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 195
  (Polychromatic418967fa.accept_20_5_8_15_1_9845 5 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 108 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 4 108 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 195 3 1 36 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 108 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 108 195
  (Polychromatic418967fa.accept_21_1_3_6_1_8321 1 108 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 108 195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  89 107 195 (Eq.refl Bool.true) (allA_succ_of_accept 88 107 195 (accept_3_4 88 107 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 87 107 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 107 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 86
  107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 107 195 (accept_3_4 85
  107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 107 195
  (Polychromatic418967fa.accept_9_3_8_6_1_80 84 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 107 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 83 107 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 195 (accept_3_4 82 107 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 107 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 80
  107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 107 195 (accept_3_4 79
  107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 107 195
  (Polychromatic418967fa.accept_7_1_2_6_1_55 78 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 107 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 77 107 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 195 (accept_3_4 76 107 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 107 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 75 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 195 (Polychromatic418967fa.accept_6_2_5_3_1_16 74
  107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 195 (accept_3_4 73
  107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 195
  (Polychromatic418967fa.accept_10_2_7_5_1_605 72 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 107 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 107 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 195 (accept_3_4 70 107 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 107 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 69 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 195 (accept_3_4 67 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 65 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 195 (accept_3_4 64 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 63 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 195 (accept_3_4 61 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 195 (accept_3_4 58 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 195 (accept_3_4 55 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 195 (Polychromatic418967fa.accept_16_6_11_3_1_2198 54 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 195 (accept_3_4 52 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 195 (Polychromatic418967fa.accept_19_13_12_5_1_9943 51 107 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 195 (accept_3_4 49 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 48 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 195 (Polychromatic418967fa.accept_9_2_8_6_1_79 47 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 195 (accept_3_4 46 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 195 (accept_3_4 43 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 195 (Polychromatic418967fa.accept_10_2_7_5_1_605 42 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 41 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 195 (accept_3_4 40 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 195 (accept_3_4 37 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 195 (Polychromatic418967fa.accept_19_16_12_5_1_8578 35 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 195 (accept_3_4 34 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 195 (Polychromatic418967fa.accept_10_3_7_5_1_288 33 107
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 195 (accept_3_4 31 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 30 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 29 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 195 (accept_3_4 28 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 195 (Polychromatic418967fa.accept_18_9_17_15_1_2267 27 107 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 195 (accept_3_4 25 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 23 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 195 (accept_3_4 22 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 21 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 195 (accept_3_4 19 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 195 (accept_3_4 16 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 195 (accept_3_4 13 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 195 (Polychromatic418967fa.accept_9_3_8_6_1_80 12 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 195 (accept_3_4 10 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 195 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 195 (accept_3_4 7 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 195 (Polychromatic418967fa.accept_16_6_11_3_1_2198 6 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 195 (Polychromatic418967fa.accept_9_5_8_6_1_281 5 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 195 (accept_3_4 4 107 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 107 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 195 (accept_3_4 1 107 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 106 195
  (Eq.refl Bool.true) (allA_succ_of_accept 89 106 195 (accept_3_5 89 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 106 195 (Polychromatic418967fa.accept_19_12_11_5_1_950 88 106 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 106 195 (Polychromatic418967fa.accept_16_7_10_3_1_2210 87 106
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 106 195 (accept_3_5 86 106
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9
  85 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 106 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 84 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 106 195 (accept_3_5 83 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 106 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 82 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 81 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 106 195 (accept_3_5 80 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 106 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 79 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 106 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 78 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 106 195 (accept_3_5 77 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 106 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 76 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 106 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 106 195 (accept_3_5 74 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 73 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 72 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 106 195 (accept_3_5 71 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 106 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 70 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 195 (accept_3_5 68 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 66 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 195 (accept_3_5 65 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 64 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 195 (Polychromatic418967fa.accept_14_7_8_13_1_3161 63 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 195 (accept_3_5 62 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 195
  (Polychromatic418967fa.accept_16_12_10_3_1_4209 60 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 106 195 (accept_3_5 59 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 106 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 58 106 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 195 (accept_3_5 56 106 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 55
  106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 54 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 195 (accept_3_5 53 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 195 (Polychromatic418967fa.accept_17_1_4_8_1_5049 52 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 106 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 195 (accept_3_5 50 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 195
  (Polychromatic418967fa.accept_9_3_7_6_1_76 48 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 195 (accept_3_5 47 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 46 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 195 (accept_3_5 44 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 42 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 195 (accept_3_5 41 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 195 (Polychromatic418967fa.accept_7_5_1_6_1_163 40 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 39 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 195 (accept_3_5 38 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 195
  (Polychromatic418967fa.accept_19_17_11_5_1_7092 36 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 106 195 (accept_3_5 35 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 106 195 (Polychromatic418967fa.accept_10_4_6_5_1_74 34 106 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 195 (accept_3_5 32 106 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31
  106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 195
  (Polychromatic418967fa.accept_7_2_1_6_1_173 30 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 195 (accept_3_5 29 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 28 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 195 (Polychromatic418967fa.accept_18_9_16_15_1_2241 27 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 195 (accept_3_5 26 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 195
  (Polychromatic418967fa.accept_10_4_6_5_1_74 24 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 195 (accept_3_5 23 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 22 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 195 (accept_3_5 20 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 195 (accept_3_5 17 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 195 (Polychromatic418967fa.accept_7_2_1_6_1_173 16 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 195 (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 195 (accept_3_5 14 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 195
  (Polychromatic418967fa.accept_7_5_1_6_1_163 12 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 195 (accept_3_5 11 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 195 (Polychromatic418967fa.accept_9_1_7_6_1_75 10 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 195 (accept_3_5 8 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 195
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 6 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 195 (accept_3_5 5 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 195 (Polychromatic418967fa.accept_9_4_7_6_1_255 4 106 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 195 (Polychromatic418967fa.accept_9_3_7_6_1_76 3 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 195 (accept_3_5 2 106 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 105 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 105 195 15 6 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 105 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 89 105 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 105 195
  (Polychromatic418967fa.accept_20_8_5_15_1_9868 88 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 87 105 195 3 29 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 86 105 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 86 105 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 105 195 5 17 21 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 84 105 195 3 28 35 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 105 195
  (Polychromatic418967fa.accept_12_11_9_3_1_792 83 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 105 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 82 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 105 195 3 27 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 105 195 5 16 21 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 105 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 79 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 105 195 3 26 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 105 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 77 105 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 195
  (Polychromatic418967fa.accept_14_6_7_13_1_3158 76 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 195 15 5 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 74 105 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 73 105
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 195 3 24 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 195
  (Polychromatic418967fa.accept_12_11_9_3_1_792 71 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 105 195 5 14 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 105 195 3 23 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 105 195 (Polychromatic418967fa.accept_19_11_10_5_1_5662 68 105 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 67 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 195 3 22 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 65 105 195 5 13 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 105 195 (Polychromatic418967fa.accept_14_8_7_13_1_4113 64 105 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 195 3 21 35 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 195 15 4 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 195 (Polychromatic418967fa.accept_12_11_9_3_1_792
  59 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 105 195 3 19 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 105 195 (Polychromatic418967fa.accept_17_5_3_8_1_1697 56 105 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 105 195 5 11 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 54 105 195 3 18 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 195
  (Polychromatic418967fa.accept_12_5_9_3_1_85 53 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 195 (Polychromatic418967fa.accept_19_14_10_5_1_3073 52 105 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 195 3 17 35 65 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 105 195 5 10 21 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 105 195
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 105 195 3 16 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 105 195 (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 105 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 105 195 15 3 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 44 105 195 (Polychromatic418967fa.accept_16_12_9_3_1_5363 44 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 105 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 43 105
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 195 3 14 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 195
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 105 195 5 8 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 39 105 195 3 13 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 105 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 195 (Polychromatic418967fa.accept_12_1_9_3_1_370
  37 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 195 3 12 35 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 105 195 5 7 21 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 105 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 105 195 3 11 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 105 195 (Polychromatic418967fa.accept_19_13_10_5_1_11329 32 105 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 31 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 195 15 2 7 13 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 105 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 29 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 195 (Polychromatic418967fa.accept_16_12_9_3_1_5363 28 105
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 195 3 9 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 105 195 5 5 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 24 105 195 3 8 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 105 195 (Polychromatic418967fa.accept_12_11_9_3_1_792 23 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 105 195 3 7 35 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 105 195 5 4 21 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 105 195
  (Polychromatic418967fa.accept_12_7_9_3_1_767 19 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 105 195 3 6 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 105 195 (Polychromatic418967fa.accept_12_5_9_3_1_85 17 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 105 195 (Polychromatic418967fa.accept_19_16_10_5_1_7106 16 105
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 195 15 1 7 13 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 105 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 105 195 3 4 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 105 195 (Polychromatic418967fa.accept_12_11_9_3_1_792
  11 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 105 195 5 2 21 39
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 105 195 3 3 35 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 195
  (Polychromatic418967fa.accept_14_8_7_13_1_4113 8 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 195 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 195 3 2 35 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 105 195 5 1 21 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 105 195 (Polychromatic418967fa.accept_20_4_5_15_1_6869 4 105 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 105 195 3 1 35 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 105 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 105 195 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 105 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 105
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 104 195
  (Eq.refl Bool.true) (allA_succ_of_gcd 91 104 195 13 7 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 90 104 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 104 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 104 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 89 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 104 195 (accept_3_4 88 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 104 195 (Polychromatic418967fa.accept_21_3_20_6_1_5126 87 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 104 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 86 104 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 104 195 (accept_3_4 85 104 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 84 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 104 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 83 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 104 195 (accept_3_4 82 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 104 195 (Polychromatic418967fa.accept_10_1_4_5_1_1031 81 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 104 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 80 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 104 195 (accept_3_4 79 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 78 104 195 13 6 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 104 195 (accept_3_4 76 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253
  75 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 74 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 104 195 (accept_3_4 73 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 104 195 (Polychromatic418967fa.accept_19_15_9_5_1_5656 72 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 104 195 (accept_3_4 70 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 104 195 (Polychromatic418967fa.accept_10_9_4_5_1_616 69 104 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 104 195
  (Polychromatic418967fa.accept_11_2_5_8_1_470 68 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 104 195 (accept_3_4 67 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 66 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 65 104 195 13 5 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 64 104 195 (accept_3_4 64 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 104 195 (Polychromatic418967fa.accept_14_7_6_13_1_4111 63 104 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 195 (Polychromatic418967fa.accept_9_8_5_6_1_538 62 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 104 195 (accept_3_4 61 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 104 195
  (Polychromatic418967fa.accept_16_12_8_3_1_4241 60 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 104 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 195 (accept_3_4 58 104 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 57 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 195 (Polychromatic418967fa.accept_9_2_5_6_1_536
  56 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 104 195 (accept_3_4 55
  104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 104 195
  (Polychromatic418967fa.accept_12_6_8_3_1_82 54 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 104 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 195 13 4 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 195 (Polychromatic418967fa.accept_10_1_4_5_1_1031
  51 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 195
  (Polychromatic418967fa.accept_17_16_2_8_1_7625 50 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 104 195 (accept_3_4 49 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 48 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 195 (accept_3_4 46 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 195 (Polychromatic418967fa.accept_16_13_8_3_1_5374 45 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 104 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 44 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 104 195 (accept_3_4 43 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 104 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 42 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 195 (accept_3_4 40 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 39 104 195 13 3 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 104 195 (Polychromatic418967fa.accept_9_2_5_6_1_536 38 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 195 (accept_3_4 37 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 104 195 (Polychromatic418967fa.accept_10_6_4_5_1_615
  36 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 195 (accept_3_4 34 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 195 (Polychromatic418967fa.accept_14_5_6_13_1_3145 33 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 195 (Polychromatic418967fa.accept_19_13_9_5_1_8541 32 104 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 195 (accept_3_4 31 104 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 30 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 195
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 195 (accept_3_4 28 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 195 (Polychromatic418967fa.accept_16_11_8_3_1_3183 27 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 104 195 13 2 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 104 195 (accept_3_4 25 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 104 195 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 104 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 104 195 (accept_3_4 22 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253
  21 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 104 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 20 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 104 195 (accept_3_4 19 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 104 195 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 104 195 (accept_3_4 16 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 104 195 (Polychromatic418967fa.accept_19_15_9_5_1_5656 15 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 104 195
  (Polychromatic418967fa.accept_11_3_5_8_1_458 14 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 13 104 195 13 1 8 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 12 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 12 104 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 104 195 (accept_3_4 10 104 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 104 195 (Polychromatic418967fa.accept_10_9_4_5_1_616 9
  104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 104 195
  (Polychromatic418967fa.accept_9_8_5_6_1_538 8 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 104 195 (accept_3_4 7 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  104 195 (Polychromatic418967fa.accept_10_6_4_5_1_615 6 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 104 195 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 104 195 (accept_3_4 4 104 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 104 195 (Polychromatic418967fa.accept_9_3_5_6_1_253 3 104 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 104 195
  (Polychromatic418967fa.accept_9_2_5_6_1_536 2 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 104 195 (accept_3_4 1 104 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  195)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 93 103 195
  (Eq.refl Bool.true) (allA_succ_of_accept 92 103 195 (accept_3_5 92 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 103 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 91 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 103 195 (Polychromatic418967fa.accept_14_6_5_13_1_367 90 103
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 103 195 (accept_3_5 89 103
  195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 103 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 88 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 103 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 87 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 103 195 (accept_3_5 86 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 85 103 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 85 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 103 195 (Polychromatic418967fa.accept_8_4_7_3_1_144
  84 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 103 195 (accept_3_5 83
  103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 103 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 82 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 103 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 103 195 (accept_3_5 80 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 79 103 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 79 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 78
  103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 103 195 (accept_3_5 77
  103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 103 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 76 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 103 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 75 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 195 (accept_3_5 74 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 103 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 73 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 195 (Polychromatic418967fa.accept_10_2_3_5_1_996
  72 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 103 195 (accept_3_5 71
  103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 103 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 70 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 103 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 69 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 195 (accept_3_5 68 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 103 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 67 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 195 (Polychromatic418967fa.accept_9_3_4_6_1_252
  66 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 103 195 (accept_3_5 65
  103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 103 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 103 195 (Polychromatic418967fa.accept_16_15_7_3_1_4273 63 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 195 (accept_3_5 62 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 103 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 61 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 195 (Polychromatic418967fa.accept_7_4_5_6_1_344
  60 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 195 (accept_3_5 59
  103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 103 195
  (Polychromatic418967fa.accept_6_4_1_3_1_77 58 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 103 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 195 (accept_3_5 56 103 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 103 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 55 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 195
  (Polychromatic418967fa.accept_19_16_8_5_1_4322 54 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 195 (accept_3_5 53 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 195 (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 195 (accept_3_5 50 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 195 (Polychromatic418967fa.accept_20_9_3_15_1_3929 49 103
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 48 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 195 (accept_3_5 47 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 195 (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 195 (accept_3_5 44 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 43 103 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 195
  (Polychromatic418967fa.accept_10_2_3_5_1_996 42 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 195 (accept_3_5 41 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 195 (accept_3_5 38 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 37 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 195
  (Polychromatic418967fa.accept_7_1_5_6_1_59 36 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 195 (accept_3_5 35 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 33 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 195 (accept_3_5 32 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 195 (Polychromatic418967fa.accept_16_15_7_3_1_4273 31 103
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 195
  (Polychromatic418967fa.accept_9_3_4_6_1_252 30 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 195 (accept_3_5 29 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 195 (Polychromatic418967fa.accept_10_7_3_5_1_301 27 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 195 (accept_3_5 26 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 195 (Polychromatic418967fa.accept_7_4_5_6_1_344 25 103 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 195
  (Polychromatic418967fa.accept_17_7_1_8_1_6280 24 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 195 (accept_3_5 23 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 21 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 195 (accept_3_5 20 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 195 (Polychromatic418967fa.accept_9_1_4_6_1_5 19 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 195
  (Polychromatic418967fa.accept_7_4_5_6_1_344 18 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 195 (accept_3_5 17 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 195 (accept_3_5 14 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 195 (Polychromatic418967fa.accept_19_13_8_5_1_8539 13 103 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 195
  (Polychromatic418967fa.accept_8_4_7_3_1_144 12 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 103 195 (accept_3_5 11 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 103 195 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 195 (accept_3_5 8 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 195 (Polychromatic418967fa.accept_9_7_4_6_1_273 7 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 195
  (Polychromatic418967fa.accept_14_6_5_13_1_367 6 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 195 (accept_3_5 5 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 195 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 195 (Polychromatic418967fa.accept_9_3_4_6_1_252 3 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 195 (accept_3_5 2 103 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 195 (Polychromatic418967fa.accept_7_1_5_6_1_59 1 103 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 102
  195 (Eq.refl Bool.true) (allA_succ_of_gcd 93 102 195 3 31 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 92 102 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 92 102 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 102 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 91 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 102 195 3 30 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 89 102 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 102 195 (Polychromatic418967fa.accept_9_7_3_6_1_270
  88 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 87 102 195 3 29 34 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 102 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 86 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 85 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 102 195 3 28 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 102 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 83
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 102 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 82 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 81 102 195 3 27 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 80 102 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 102 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 195 (Polychromatic418967fa.accept_7_2_4_6_1_166
  79 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 102 195 3 26 34 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 102 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 102 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 76 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 102 195 3 25 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 102 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 74
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 73 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 195 3 24 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 71 102 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 102 195 (Polychromatic418967fa.accept_9_7_3_6_1_270
  70 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 102 195 3 23 34 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 102 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 102 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 67 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 102 195 3 22 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 65
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 64 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 102 195 3 21 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 102 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 62 102 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 61
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 195 3 20 34 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 59 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 102 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 58 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 102 195 3 19 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 102 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 56
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 55 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 195 3 18 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 102 195 (Polychromatic418967fa.accept_7_3_4_6_1_329
  52 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 102 195 3 17 34 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 102 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 50 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 102 195 3 16 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 102 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 47
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 46 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 102 195 3 15 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 102 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 102 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 102 195 (Polychromatic418967fa.accept_9_7_3_6_1_270
  43 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 195 3 14 34 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 102 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 40 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 102 195 3 13 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 102 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 38
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 102 195 3 12 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 102 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 35 102 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 102 195 (Polychromatic418967fa.accept_9_7_3_6_1_270
  34 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 102 195 3 11 34 65
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 102 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 32 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 102 195 (Polychromatic418967fa.accept_7_3_4_6_1_329 31 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 102 195 3 10 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 195
  (Polychromatic418967fa.accept_9_1_3_6_1_70 28 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 102 195 3 9 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 102 195 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 195 3 8 34 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 195
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 102 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 22 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 102 195 3 7 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 102 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 20
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 102 195
  (Polychromatic418967fa.accept_7_5_4_6_1_167 19 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 195 3 6 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 16 102 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 102 195 3 5 34 65 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 102 195
  (Polychromatic418967fa.accept_9_5_3_6_1_269 14 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 102 195 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 195 3 4 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 195 (Polychromatic418967fa.accept_9_2_3_6_1_88 11
  102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 102 195
  (Polychromatic418967fa.accept_7_3_4_6_1_329 10 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 102 195 3 3 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 102 195 (Polychromatic418967fa.accept_9_8_3_6_1_533 8 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 195 (Polychromatic418967fa.accept_9_7_3_6_1_270 7 102 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 102 195 3 2 34 65 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 102 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 102 195 (Polychromatic418967fa.accept_9_4_3_6_1_532 4 102 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 195 3 1 34 65 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 195 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 102 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 102 195
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 102 195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 95 101 195 (Eq.refl Bool.true) (allA_succ_of_accept 94 101 195 (accept_3_4 94 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 101 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 101 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 92 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 101 195 (accept_3_4 91 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 101 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 90 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 101 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 89 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 195 (accept_3_4 88 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 195 (Polychromatic418967fa.accept_17_2_16_8_1_3881 87 101 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 86 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 195 (accept_3_4 85 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 84 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 195 (Polychromatic418967fa.accept_19_7_6_5_1_4320 83 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 195 (accept_3_4 82 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 101 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 80 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 195 (accept_3_4 79 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 78 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 77 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 195 (accept_3_4 76 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 75 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 195 (accept_3_4 73 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 71 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 195 (accept_3_4 70 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 69 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 68 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 195 (accept_3_4 67 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 195 (accept_3_4 64 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 195 (Polychromatic418967fa.accept_18_9_11_15_1_4616 63 101 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 195 (accept_3_4 61 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 59 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 195 (accept_3_4 58 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 57 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 195 (accept_3_4 55 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 101 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 195 (accept_3_4 52 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 195 (accept_3_4 49 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 48 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 195 (Polychromatic418967fa.accept_20_7_1_15_1_2700 47 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 195 (accept_3_4 46 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 101
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 195 (accept_3_4 43 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 41 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 195 (accept_3_4 40 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 101 195 (accept_3_4 37 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 101 195 (Polychromatic418967fa.accept_10_6_1_5_1_1024 36 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 101 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 35 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 195 (accept_3_4 34 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 195 (Polychromatic418967fa.accept_12_9_5_3_1_782 33 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 195 (accept_3_4 31 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 195 (Polychromatic418967fa.accept_10_9_1_5_1_594 29 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 195 (accept_3_4 28 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 195 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 101
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 195 (accept_3_4 25 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 195 (Polychromatic418967fa.accept_10_4_1_5_1_1018 24 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 195 (accept_3_4 22 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 21 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 195 (accept_3_4 19 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 195 (Polychromatic418967fa.accept_9_8_2_6_1_875 17 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 195 (accept_3_4 16 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 195 (Polychromatic418967fa.accept_19_15_6_5_1_4356 15 101 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 195 (accept_3_4 13 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 12 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 195 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 195 (accept_3_4 10 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 195 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 195
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 195 (accept_3_4 7 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 195 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 195 (Polychromatic418967fa.accept_9_5_2_6_1_265 5 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 195 (accept_3_4 4 101 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 195 (Polychromatic418967fa.accept_9_3_2_6_1_264 3 101 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 195
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 195 (accept_3_4 1 101 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 96 100
  195 (Eq.refl Bool.true) (allA_succ_of_gcd 95 100 195 5 19 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 94 100 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 94 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 100 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 93 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 100 195 (accept_3_5 92 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  91 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 91 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 90 100 195 5 18 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 89 100 195 (accept_3_5 89 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 100 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 88 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 100 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 100 195 (accept_3_5 86 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 100 195 5 17 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 100 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 84 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 100 195 (accept_3_5 83 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 100 195 (Polychromatic418967fa.accept_22_16_12_19_1_11328 82 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 100 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 100 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 100 195 5 16 20 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 100 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 79 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 100 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 100 195 (accept_3_5 77 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 100 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 76 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 75 100 195 5 15 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 74 100 195 (accept_3_5 74 100 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 73 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 100 195
  (Polychromatic418967fa.accept_16_8_4_3_1_3146 72 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 100 195 (accept_3_5 71 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  100 195 5 14 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 100 195 (Polychromatic418967fa.accept_26_17_22_13_1_11327 69 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 100 195 (accept_3_5 68 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 100 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 100 195
  (Polychromatic418967fa.accept_7_3_2_6_1_56 66 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 65 100 195 5 13 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 64 100 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 64 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 100 195 (Polychromatic418967fa.accept_8_7_4_3_1_156
  63 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 100 195 (accept_3_5 62
  100 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 100 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 61 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 100 195 5 12 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 100 195 (accept_3_5 59 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 100 195 (Polychromatic418967fa.accept_9_4_1_6_1_284 58 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 100 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 100 195 (accept_3_5 56 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 55 100 195 5 11 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 54 100 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 54 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 100 195 (accept_3_5 53 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 100 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 52 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 100 195 (Polychromatic418967fa.accept_21_9_16_6_1_5134 51 100 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 100 195 5 10 20 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 100 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 49 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 100 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 48 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 100 195 (accept_3_5 47 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 100 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 46 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 100 195 5 9 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 100 195 (accept_3_5 44 100 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 100 195
  (Polychromatic418967fa.accept_12_6_4_3_1_361 42 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 100 195 (accept_3_5 41 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40
  100 195 5 8 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  39 100 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 100 195 (accept_3_5 38 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 100 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 35 100 195 5 7 20 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 100 195
  (Polychromatic418967fa.accept_9_7_1_6_1_261 34 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 100 195 (Polychromatic418967fa.accept_16_1_4_3_1_3148 33 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 100 195 (accept_3_5 32 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 100 195 5 6 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 100 195 (accept_3_5 29 100 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 100 195 (Polychromatic418967fa.accept_16_12_4_3_1_4295 28 100
  195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 100 195
  (Polychromatic418967fa.accept_17_10_15_8_1_6324 27 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 100 195 (accept_3_5 26 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 25 100 195 5 5 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 100 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 100 195 (accept_3_5 23 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 100 195 (Polychromatic418967fa.accept_7_1_2_6_1_55 22 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 100 195 (Polychromatic418967fa.accept_9_3_1_6_1_86 21
  100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 100 195 5 4 20 39 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 100 195
  (Polychromatic418967fa.accept_6_1_4_3_1_14 19 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 100 195 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 100 195 (accept_3_5 17 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 100 195 (Polychromatic418967fa.accept_9_7_1_6_1_261 16 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 100 195 5 3 20 39 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 100 195 (accept_3_5 14 100 195 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 100 195
  (Polychromatic418967fa.accept_9_3_1_6_1_86 12 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 100 195 (accept_3_5 11 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  100 195 5 2 20 39 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 100 195 (Polychromatic418967fa.accept_18_9_10_15_1_7254 9 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 100 195 (accept_3_5 8 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 100 195 (Polychromatic418967fa.accept_12_6_4_3_1_361 6 100 195
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 100 195 5 1 20 39 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 100 195
  (Polychromatic418967fa.accept_7_4_2_6_1_337 4 100 195 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 100 195 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 100 195 (accept_3_5 2 100 195 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 100 195 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 100 195 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 100
  195))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_195_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


