-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch192
-- name    : Polychromatic418967fa_Branch192
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:22:35.530183+00:00
-- url     : https://prove2.me/theorems/bf6a607a-9a8d-4298-89a3-664d1fc0ba6c
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch192_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_192 : allB 192 192 :=
  allB_succ' 2 191 192 (Eq.refl Bool.true) (allA_succ_of_accept 1 191 192 (accept_3_4 1 191 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 191 192)) (allB_succ' 3 190 192 (Eq.refl Bool.true) (allA_succ_of_gcd 2 190 192 2 1 95
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 190 192
  (Polychromatic418967fa.accept_25_1_15_17_1_11179 1 190 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 190 192))) (allB_succ' 4 189 192 (Eq.refl Bool.true) (allA_succ_of_gcd 3 189 192 3 1 63 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 192
  (Polychromatic418967fa.accept_20_2_9_12_1_2546 2 189 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 189 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 192)))) (allB_succ' 5 188 192 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  188 192 4 1 47 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 188 192 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 188 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 188 192 2 1 94 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 188 192 (accept_3_4 1 188 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188
  192))))) (allB_succ' 6 187 192 (Eq.refl Bool.true) (allA_succ_of_accept 5 187 192 (accept_3_5 5 187 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 187 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 187 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 187 192
  (Polychromatic418967fa.accept_15_3_7_12_1_372 3 187 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 187 192 (accept_3_5 2 187 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  187 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 187 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 187 192)))))) (allB_succ' 7 186 192 (Eq.refl Bool.true) (allA_succ_of_gcd 6 186 192 6 1 31 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 192
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 186 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 186 192 2 2 93 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 186 192 3 1 62 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 186 192 2 1 93 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 186 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 186 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 186 192))))))) (allB_succ' 8 185 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 185 192 (accept_3_4 7 185 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 185 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 192 (Polychromatic418967fa.accept_19_5_14_2_1_1716 5 185 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 192 (accept_3_4 4 185 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 192 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 185 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 185 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 192 (accept_3_4 1 185 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  192)))))))) (allB_succ' 9 184 192 (Eq.refl Bool.true) (allA_succ_of_gcd 8 184 192 8 1 23 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 192
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 184 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 184 192 2 3 92 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 192 (accept_3_5 5 184 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  192 4 1 46 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 192 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 184 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 192 2 1 92 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 184 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 184 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 192))))))))) (allB_succ' 10 183 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 183 192 3 3 61 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 183 192 (Polychromatic418967fa.accept_15_8_3_12_1_1657 8 183 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 192 (Polychromatic418967fa.accept_15_7_3_12_1_365 7 183 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 183 192 3 2 61 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 183 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 183 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 183 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 192 3 1 61 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 183 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 192
  (Polychromatic418967fa.accept_10_1_3_2_1_220 1 183 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 183 192)))))))))) (allB_succ' 11 182 192 (Eq.refl Bool.true) (allA_succ_of_gcd 10 182 192 2 5 91 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 192
  (Polychromatic418967fa.accept_17_9_12_5_1_219 9 182 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 192 2 4 91 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 192 (accept_3_4 7 182 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  192 2 3 91 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 182 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 192 2 2 91 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 182 192 (Polychromatic418967fa.accept_15_3_2_12_1_2469 3 182 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 192 2 1 91 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 192 (accept_3_4 1 182 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 182 192))))))))))) (allB_succ' 12 181 192 (Eq.refl Bool.true) (allA_succ_of_accept 11
  181 192 (accept_3_5 11 181 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 181 192
  (Polychromatic418967fa.accept_21_10_13_3_1_11141 10 181 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 181 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 181 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 192 (accept_3_5 8 181 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 181 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 181 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 181 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 181 192 (accept_3_5 5 181 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  181 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 181 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 181 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 181 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 192 (accept_3_5 2 181 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 192 (Polychromatic418967fa.accept_22_1_5_16_1_11178 1 181 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 181 192)))))))))))) (allB_succ' 13 180 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 12 180 192 12 1 15 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 192 (Polychromatic418967fa.accept_19_11_9_2_1_1729 11 180 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 192 2 5 90 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 192 3 3 60 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 192 4 2 45 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 192
  (Polychromatic418967fa.accept_19_7_9_2_1_4090 7 180 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 192 6 1 30 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 192 (Polychromatic418967fa.accept_14_5_12_10_1_2985 5 180 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 192 4 1 45 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 192 3 1 60 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 180 192 2 1 90 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 180 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 192))))))))))))) (allB_succ' 14 179 192
  (Eq.refl Bool.true) (allA_succ_of_accept 13 179 192 (accept_3_4 13 179 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 179 192 (Polychromatic418967fa.accept_17_12_9_5_1_799 12 179 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 179 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 192 (accept_3_4 10 179 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 192 (Polychromatic418967fa.accept_15_9_14_12_1_913
  9 179 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 179 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 192 (accept_3_4 7 179 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 179 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 179 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 192 (accept_3_4 4 179 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 192 (Polychromatic418967fa.accept_23_3_18_8_1_7822 3 179 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 179 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 192 (accept_3_4 1 179 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  192)))))))))))))) (allB_succ' 15 178 192 (Eq.refl Bool.true) (allA_succ_of_gcd 14 178 192 2 7 89 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 192
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 178 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 192 2 6 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 178 192 (accept_3_5 11 178 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  178 192 2 5 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 178 192 (Polychromatic418967fa.accept_18_9_16_12_1_1143 9 178 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 178 192 2 4 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 178 192 (Polychromatic418967fa.accept_21_7_10_3_1_1049 7 178 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 178 192 2 3 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 178 192 (accept_3_5 5 178 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178 192 2 2 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 178 192 (Polychromatic418967fa.accept_15_3_13_12_1_348 3 178 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 178 192 2 1 89 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 178 192
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 178 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 178 192))))))))))))))) (allB_succ' 16 177 192 (Eq.refl Bool.true) (allA_succ_of_gcd 15 177 192 3 5 59 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 192
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 177 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 177 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 177 192 3 4 59 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 177 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  177 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 192
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 177 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 177 192 3 3 59 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 177 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 8 177 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 177 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 192 3 2 59 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 5 177 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 177 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 192 3 1 59 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 177 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 177 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 177 192)))))))))))))))) (allB_succ' 17 176 192 (Eq.refl Bool.true) (allA_succ_of_gcd 16 176 192 16 1 11 12
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 192
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 176 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 192 2 7 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 176 192 (accept_3_4 13 176 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12
  176 192 4 3 44 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  11 176 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 176 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 176 192 2 5 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 176 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 176 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 192 8 1 22 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 192 (accept_3_4 7 176 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 192 2 3 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 176 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 176 192 4 1 44 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 176 192
  (Polychromatic418967fa.accept_13_3_7_10_1_668 3 176 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 176 192 2 1 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 176 192 (accept_3_4 1 176 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  192))))))))))))))))) (allB_succ' 18 175 192 (Eq.refl Bool.true) (allA_succ_of_accept 17 175 192 (accept_3_5 17 175 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 175 192 (Polychromatic418967fa.accept_9_7_4_3_1_204
  16 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 175 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 175 192 (accept_3_5 14 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 175 192 (Polychromatic418967fa.accept_10_3_5_2_1_38 13 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 175 192 (Polychromatic418967fa.accept_13_12_6_10_1_667 12 175 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 192 (accept_3_5 11 175 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 175 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 175 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 175 192
  (Polychromatic418967fa.accept_13_9_6_10_1_666 9 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 175 192 (accept_3_5 8 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  175 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 175 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 175 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 175 192 (accept_3_5 5 175 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 175 192 (Polychromatic418967fa.accept_11_4_10_5_1_1202 4 175 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 175 192
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 175 192 (accept_3_5 2 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  175 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 175 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 175 192)))))))))))))))))) (allB_succ' 19 174 192 (Eq.refl Bool.true) (allA_succ_of_gcd 18 174
  192 6 3 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  174 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 174 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 174 192 2 8 87 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 192 3 5 58 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 192 2 7 87 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 174 192 (Polychromatic418967fa.accept_21_13_6_3_1_3381 13 174 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 174 192 6 2 29 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 174 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 174 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 174 192 2 5 87 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 174 192 3 3 58 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 174 192 2 4 87 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 174 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 192 6 1 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 192 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 174 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 192 2 2 87 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 192 3 1 58 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 192 2 1 87 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 192
  (Polychromatic418967fa.accept_17_1_4_5_1_3501 1 174 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 174 192))))))))))))))))))) (allB_succ' 20 173 192 (Eq.refl Bool.true) (allA_succ_of_accept 19 173 192
  (accept_3_4 19 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 173 192
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 173 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 173 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 192 (accept_3_4 16 173 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 173 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 173 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 192 (Polychromatic418967fa.accept_9_5_2_3_1_194
  14 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 173 192 (accept_3_4 13
  173 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 173 192
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 192 (Polychromatic418967fa.accept_10_1_3_2_1_220 11 173 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 192 (accept_3_4 10 173 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 173 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 192 (accept_3_4 7 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 173 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 192 (accept_3_4 4 173 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 192 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 173 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 192 (accept_3_4 1 173 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  192)))))))))))))))))))) (allB_succ' 21 172 192 (Eq.refl Bool.true) (allA_succ_of_gcd 20 172 192 4 5 43 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 192
  (Polychromatic418967fa.accept_13_6_3_10_1_698 19 172 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 172 192 2 9 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 172 192 (accept_3_5 17 172 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  172 192 4 4 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 172 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 172 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 172 192 2 7 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 172 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 172 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 172 192 4 3 43 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 172 192 (accept_3_5 11 172 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 172 192 2 5 86 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 172 192
  (Polychromatic418967fa.accept_11_9_7_5_1_749 9 172 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 172 192 4 2 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 172 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 172 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 172 192 2 3 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 172 192 (accept_3_5 5 172 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 172 192 4 1 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 172 192 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 172 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 172 192 2 1 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 172 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 1
  172 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 192)))))))))))))))))))))
  (allB_succ' 22 171 192 (Eq.refl Bool.true) (allA_succ_of_gcd 21 171 192 3 7 57 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 192
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 171 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 171 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 192 3 6 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 192 (Polychromatic418967fa.accept_15_2_6_12_1_1613
  17 171 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 192
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 171 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 171 192 3 5 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 171 192 (Polychromatic418967fa.accept_25_14_21_17_1_11177 14 171 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 192 (Polychromatic418967fa.accept_10_3_1_2_1_521
  13 171 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 192 3 4 57 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 192
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 171 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 192 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 171 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 192 3 3 57 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 192
  (Polychromatic418967fa.accept_13_8_2_10_1_652 8 171 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 192 (Polychromatic418967fa.accept_14_7_3_10_1_1364 7 171 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 192 3 2 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 192 (Polychromatic418967fa.accept_13_5_2_10_1_248 5 171 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 192
  (Polychromatic418967fa.accept_17_4_1_5_1_2554 4 171 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 171 192 3 1 57 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 171 192 (Polychromatic418967fa.accept_15_2_6_12_1_1613 2 171 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 192 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 171 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171 192)))))))))))))))))))))) (allB_succ' 23
  170 192 (Eq.refl Bool.true) (allA_succ_of_gcd 22 170 192 2 11 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 192 (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 170
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 170 192 2 10 85 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 170 192 (accept_3_4 19
  170 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 170 192 2 9 85 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 170 192
  (Polychromatic418967fa.accept_13_4_1_10_1_693 17 170 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 170 192 2 8 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 170 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 170 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 170 192 2 7 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 170 192 (accept_3_4 13 170 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 170 192 2 6 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 170 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 170 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 192 2 5 85 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 192
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 170 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 192 2 4 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 192 (accept_3_4 7 170 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  192 2 3 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 170 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 192 2 2 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 170 192 (Polychromatic418967fa.accept_18_3_8_12_1_3283 3 170 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 192 2 1 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 192 (accept_3_4 1 170 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 170 192))))))))))))))))))))))) (allB_succ' 24 169 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 169 192 (accept_3_5 23 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 169 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 169 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 169 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 169 192 (accept_3_5 20 169 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 169 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 169 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 169 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 169 192 (accept_3_5 17 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 169 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 169 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 169 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 169 192 (accept_3_5 14 169 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 169 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 169 192 (accept_3_5 11 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 169 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 169 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 169 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 192 (accept_3_5 8 169 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 192 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 169 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 192
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 192 (accept_3_5 5 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 169 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 192 (Polychromatic418967fa.accept_18_3_7_12_1_1196 3 169 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 192 (accept_3_5 2 169 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 169 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 192)))))))))))))))))))))))) (allB_succ' 25
  168 192 (Eq.refl Bool.true) (allA_succ_of_gcd 24 168 192 24 1 7 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 168 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 192 2 11 84 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 168 192 3 7 56 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 168 192 4 5 42 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 192
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 168 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 192 6 3 28 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 168 192 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 168 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 192 8 2 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 168 192 3 5 56 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 168 192 2 7 84 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 13
  168 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 192 12 1 14 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 192
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 168 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 192 2 5 84 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 168 192 3 3 56 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 168 192 8 1 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 168 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168 192 6 1 28 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 168 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 168 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 192 4 1 42 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 192 3 1 56 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 192 2 1 84 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 192
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 168 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 192))))))))))))))))))))))))) (allB_succ' 26 167 192 (Eq.refl Bool.true) (allA_succ_of_accept 25 167 192
  (accept_3_4 25 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 167 192
  (Polychromatic418967fa.accept_9_6_5_3_1_205 24 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 167 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 167 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 192 (accept_3_4 22 167 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 167 192 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 167 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 192 (accept_3_4 19 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 167 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 192 (accept_3_4 16 167 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 167 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 192
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 192 (accept_3_4 13 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 192 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 167 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 192 (accept_3_4 10 167 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 167 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 192 (accept_3_4 7 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 167 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 192 (accept_3_4 4 167 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 192 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 167 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 192 (accept_3_4 1 167 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  192)))))))))))))))))))))))))) (allB_succ' 27 166 192 (Eq.refl Bool.true) (allA_succ_of_gcd 26 166 192 2 13 83 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 192
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 166 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 192 2 12 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 192 (accept_3_5 23 166 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 192 2 11 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 192 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 166 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 192 2 10 83 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 192
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 166 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 192 2 9 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 166 192 (accept_3_5 17 166 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  166 192 2 8 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 166 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 166 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 166 192 2 7 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 166 192 (Polychromatic418967fa.accept_15_13_1_12_1_1638 13 166 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 166 192 2 6 83 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 166 192 (accept_3_5 11
  166 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 166 192 2 5 83 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 166 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 166 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 166 192 2 4 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 166 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 166 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 166 192 2 3 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 166 192 (accept_3_5 5 166 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 166 192 2 2 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 166 192 (Polychromatic418967fa.accept_23_3_5_8_1_11176 3 166 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 166 192 2 1 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 166 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 1
  166 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 192)))))))))))))))))))))))))))
  (allB_succ' 28 165 192 (Eq.refl Bool.true) (allA_succ_of_gcd 27 165 192 3 9 55 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 165 192
  (Polychromatic418967fa.accept_17_9_12_5_1_219 26 165 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 165 192 (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 165 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 165 192 3 8 55 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 192
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 165 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 165 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 165 192 3 7 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 165 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 20
  165 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 192
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 165 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 165 192 3 6 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 165 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 165 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 192 (Polychromatic418967fa.accept_19_16_13_2_1_6920 16 165
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 192 3 5 55 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 192
  (Polychromatic418967fa.accept_13_1_9_10_1_625 14 165 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 165 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 192 3 4 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 192
  (Polychromatic418967fa.accept_19_11_13_2_1_9770 11 165 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 165 192 (Polychromatic418967fa.accept_17_10_12_5_1_6028 10 165 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 192 3 3 55 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 165 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 165 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 192 3 2 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 192 (Polychromatic418967fa.accept_21_5_18_3_1_4908 5 165 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 192
  (Polychromatic418967fa.accept_21_4_18_3_1_11175 4 165 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 192 3 1 55 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 192 (Polychromatic418967fa.accept_18_2_3_12_1_1155 2 165 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 165 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 192)))))))))))))))))))))))))))) (allB_succ'
  29 164 192 (Eq.refl Bool.true) (allA_succ_of_gcd 28 164 192 4 7 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 164 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 192 2 13 82 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 192 (accept_3_4 25
  164 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 192 4 6 41 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 164 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 164 192 2 11 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 164 192 (Polychromatic418967fa.accept_18_3_2_12_1_5751 21 164 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 164 192 4 5 41 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 164 192 (accept_3_4 19 164 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 164 192 2 9 82 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 164 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 164 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 164 192 4 4 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 164 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 164 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 192 2 7 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 192 (accept_3_4 13 164 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 192 4 3 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 192 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 164
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 192 2 5 82 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 192
  (Polychromatic418967fa.accept_15_9_14_12_1_913 9 164 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 192 4 2 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 192 (accept_3_4 7 164 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  192 2 3 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 164 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 192 4 1 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 164 192 (Polychromatic418967fa.accept_18_3_2_12_1_5751 3 164 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 192 2 1 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 192 (accept_3_4 1 164 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 164 192))))))))))))))))))))))))))))) (allB_succ' 30 163 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 163 192 (accept_3_5 29 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 163 192 (Polychromatic418967fa.accept_19_9_11_2_1_5436 28 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 163 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 163 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 163 192 (accept_3_5 26 163 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 163 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 163 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 163 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 163 192 (accept_3_5 23 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 163 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 163 192 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 163 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 163 192 (accept_3_5 20 163 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 163 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 163 192
  (Polychromatic418967fa.accept_11_7_9_5_1_338 18 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 163 192 (accept_3_5 17 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 163 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 163 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 163 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 163 192 (accept_3_5 14 163 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 163 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 163 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 163 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 163 192 (accept_3_5 11 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 163 192 (Polychromatic418967fa.accept_15_10_13_12_1_3384 10 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 192 (Polychromatic418967fa.accept_19_9_11_2_1_5436 9 163 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 163 192 (accept_3_5 8 163 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 163 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 163 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 163 192
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 163 192 (accept_3_5 5 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  163 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 163 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 163 192 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 163 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 163 192 (accept_3_5 2 163 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 163 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 163 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 163 192)))))))))))))))))))))))))))))) (allB_succ' 31 162
  192 (Eq.refl Bool.true) (allA_succ_of_gcd 30 162 192 6 5 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 162 192 (Polychromatic418967fa.accept_13_3_6_10_1_2658 29 162
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 192 2 14 81 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 162 192 3 9 54 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 162 192 2 13 81 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 162 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 162 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 192 6 4 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 162 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 162 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 192 2 11 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 162 192 3 7 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 162 192 2 10 81 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 162 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 162 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 192 6 3 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 162 192 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 162 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 192 2 8 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 162 192 3 5 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 162 192 2 7 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 162 192 (Polychromatic418967fa.accept_11_2_8_5_1_1219
  13 162 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 162 192 6 2 27 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 162 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 162 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 162 192 2 5 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 162 192 3 3 54 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 162 192 2 4 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 192 (Polychromatic418967fa.accept_17_7_9_5_1_2588 7 162 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 192 6 1 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 162 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 162 192 2 2 81 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 162 192 3 1 54 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 162 192 2 1 81 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 192
  (Polychromatic418967fa.accept_21_1_15_3_1_4817 1 162 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 162 192))))))))))))))))))))))))))))))) (allB_succ' 32 161 192 (Eq.refl Bool.true) (allA_succ_of_accept 31
  161 192 (accept_3_4 31 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 161 192
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 161 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 161 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 192 (accept_3_4 28 161 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 161 192 (Polychromatic418967fa.accept_18_9_17_12_1_462 27 161 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 192
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 192 (accept_3_4 25 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 161 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 192 (accept_3_4 22 161 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 192 (Polychromatic418967fa.accept_13_8_5_10_1_2701 21 161 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 192 (accept_3_4 19 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 192 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 192 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 161 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 192 (accept_3_4 16 161 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 161 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 192
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 192 (accept_3_4 13 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 192 (Polychromatic418967fa.accept_17_12_8_5_1_6018 12 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 161 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 192 (accept_3_4 10 161 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 161 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 192
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 192 (accept_3_4 7 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 161 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 192 (accept_3_4 4 161 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 161 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 192 (accept_3_4 1 161 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  192)))))))))))))))))))))))))))))))) (allB_succ' 33 160 192 (Eq.refl Bool.true) (allA_succ_of_gcd 32 160 192 32 1 5 6
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 160 192
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 160 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 160 192 2 15 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 160 192 (accept_3_5 29 160 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 160 192 4 7 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 160 192 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 160 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 160 192 2 13 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 160 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 25
  160 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 160 192 8 3 20 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 160 192 (accept_3_5 23
  160 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 160 192 2 11 80 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 160 192
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 160 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 160 192 4 5 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 160 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 160 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 160 192 2 9 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 160 192 (accept_3_5 17 160 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 160 192 16 1 10 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 160 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 160 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 160 192 2 7 80 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 160 192
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 160 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 160 192 4 3 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 160 192 (accept_3_5 11 160 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  160 192 2 5 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 160 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 160 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 160 192 8 1 20 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 160 192 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 160 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 160 192 2 3 80 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 160 192 (accept_3_5 5 160 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 160 192 4 1 40 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 160 192 (Polychromatic418967fa.accept_14_3_6_10_1_752 3 160 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 160 192 2 1 80 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 160 192
  (Polychromatic418967fa.accept_9_1_7_3_1_41 1 160 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 160 192))))))))))))))))))))))))))))))))) (allB_succ' 34 159 192 (Eq.refl Bool.true) (allA_succ_of_gcd 33 159
  192 3 11 53 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  159 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 159 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 159 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 159 192 3 10 53 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 159 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 159 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 159 192 3 9 53 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 159 192 (Polychromatic418967fa.accept_9_8_6_3_1_457 26
  159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 192
  (Polychromatic418967fa.accept_9_7_6_3_1_456 25 159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 159 192 3 8 53 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 159 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 159 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 159 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 192 3 7 53 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 192
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 159 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 192 3 6 53 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 192 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 16 159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 159 192 3 5 53 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 159 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 159 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 159 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 192 3 4 53 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 192
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 159 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 192 3 3 53 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 159 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 192
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 192 3 2 53 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 159 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 159 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 192 3 1 53 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 2 159 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 159 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159 192)))))))))))))))))))))))))))))))))) (allB_succ' 35 158 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 158 192 2 17 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 158 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 158 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 158 192 2 16 79 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 158 192 (accept_3_4 31 158 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 158 192 2 15 79 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 158 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 158 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 158 192 2 14 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 158 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 158 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 158 192 2 13 79 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 158 192 (accept_3_4 25 158 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 158 192 2 12 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 158 192 (Polychromatic418967fa.accept_19_4_6_2_1_6906
  23 158 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 192 2 11 79 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 192
  (Polychromatic418967fa.accept_11_10_4_5_1_359 21 158 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 192 2 10 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 192 (accept_3_4 19 158 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 192 2 9 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 158 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 158 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 192 2 8 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 15
  158 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 158 192 2 7 79 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 158 192 (accept_3_4 13
  158 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 158 192 2 6 79 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 158 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 158 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 158 192 2 5 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 158 192 (Polychromatic418967fa.accept_22_9_4_16_1_4545 9 158 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 158 192 2 4 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 158 192 (accept_3_4 7 158 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 158 192 2 3 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 158 192 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 158 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 158 192 2 2 79 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 158 192 (Polychromatic418967fa.accept_13_3_2_10_1_2697
  3 158 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 192 2 1 79 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 192 (accept_3_4 1
  158 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158 192))))))))))))))))))))))))))))))))))) (allB_succ' 36
  157 192 (Eq.refl Bool.true) (allA_succ_of_accept 35 157 192 (accept_3_5 35 157 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 157 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 157 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 157 192 (Polychromatic418967fa.accept_9_6_4_3_1_203
  33 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 157 192 (accept_3_5 32
  157 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 157 192
  (Polychromatic418967fa.accept_22_9_3_16_1_11174 31 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 157 192 (Polychromatic418967fa.accept_11_8_3_5_1_355 30 157 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 157 192 (accept_3_5 29 157 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 157 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 157 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 157 192
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 157 192 (accept_3_5 26 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 157 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 157 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 157 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 157 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 192 (accept_3_5 23 157 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 157 192 (Polychromatic418967fa.accept_13_9_1_10_1_647
  22 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 192
  (Polychromatic418967fa.accept_14_7_3_10_1_1364 21 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 192 (accept_3_5 20 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 192 (Polychromatic418967fa.accept_15_3_7_12_1_372 18 157 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 192 (accept_3_5 17 157 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 157 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 192 (accept_3_5 14 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 192 (Polychromatic418967fa.accept_14_13_3_10_1_2159 13 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 192 (Polychromatic418967fa.accept_21_12_10_3_1_11112 12 157 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 192 (accept_3_5 11 157 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 157 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 192
  (Polychromatic418967fa.accept_10_9_7_2_1_887 9 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 192 (accept_3_5 8 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 157 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 192 (accept_3_5 5 157 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 192 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 157 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 192
  (Polychromatic418967fa.accept_15_3_7_12_1_372 3 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 192 (accept_3_5 2 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 157 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 192)))))))))))))))))))))))))))))))))))) (allB_succ' 37 156 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 156 192 12 3 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 192 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 156 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 192 2 17 78 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 156 192 3 11 52 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 156 192 4 8 39 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 192
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 156 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 192 6 5 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 156 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 156 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 192 4 7 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 156 192 3 9 52 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 156 192 2 13 78 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 192
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 25 156 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 156 192 12 2 13 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 156 192 (Polychromatic418967fa.accept_17_6_3_5_1_3657 23 156 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 192 2 11 78 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 156 192 3 7 52 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 156 192 4 5 39 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 156 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 156 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 192 6 3 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 192 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 156 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 192 4 4 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 156 192 3 5 52 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 156 192 2 7 78 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 13
  156 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 192 12 1 13 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 192
  (Polychromatic418967fa.accept_10_1_6_2_1_867 11 156 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 192 2 5 78 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 156 192 3 3 52 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 156 192 4 2 39 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 192 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 156 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 192 6 1 26 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 156 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 192 4 1 39 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 156 192 3 1 52 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 156 192 2 1 78 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 1 156 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 156 192))))))))))))))))))))))))))))))))))))) (allB_succ' 38 155 192 (Eq.refl Bool.true) (allA_succ_of_accept
  37 155 192 (accept_3_4 37 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 155 192
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 155 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 155 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 192 (accept_3_4 34 155 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 155 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 192 (Polychromatic418967fa.accept_7_4_1_3_1_277
  32 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 192 (accept_3_4 31
  155 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 155 192 (Polychromatic418967fa.accept_22_7_1_16_1_7933 29 155 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 192 (accept_3_4 28 155 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 155 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 155 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 26 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 155 192 (accept_3_4 25 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 155 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 155 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 155 192 (accept_3_4 22 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 155 192 (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 155 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 155 192
  (Polychromatic418967fa.accept_13_7_12_10_1_640 20 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 155 192 (accept_3_4 19 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 155 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 155 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 155 192 (accept_3_4 16 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 155 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 155 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 155 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 155 192 (accept_3_4 13 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 155 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 155 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 11 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 155 192 (accept_3_4 10 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 155 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 155 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 155 192 (accept_3_4 7 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  155 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 155 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 155 192 (accept_3_4 4 155 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 155 192 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 155 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 155 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 155 192 (accept_3_4 1 155 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 155
  192)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 154 192 (Eq.refl Bool.true) (allA_succ_of_gcd 38 154 192 2 19
  77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 154 192
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 154 192 2 18 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 154 192 (accept_3_5 35 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 154 192 2 17 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 154 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 154 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 154 192 2 16 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 154 192
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 154 192 2 15 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 154 192 (accept_3_5 29 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 154 192 2 14 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 154 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 154 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 154 192 2 13 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 154 192
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 154 192 2 12 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 154 192 (accept_3_5 23 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 154 192 2 11 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 154 192 (Polychromatic418967fa.accept_13_8_11_10_1_636 21 154 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 154 192 2 10 77 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 154 192
  (Polychromatic418967fa.accept_36_19_10_12_1_11173 19 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 154 192 2 9 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 154 192 (accept_3_5 17 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 154 192 2 8 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 154 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 154 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 154 192 2 7 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 154 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 13
  154 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 154 192 2 6 77 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 154 192 (accept_3_5 11
  154 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 154 192 2 5 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 154 192
  (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 154 192 2 4 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 154 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 154 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 154 192 2 3 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 154 192 (accept_3_5 5 154 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 154 192 2 2 77 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 154 192 (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 154 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 154 192 2 1 77 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 154 192
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 1 154 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 154 192))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 153 192 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 153 192 3 13 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 153 192 (Polychromatic418967fa.accept_15_8_3_12_1_1657 38 153 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 153 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 153 192 3 12 51 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 153 192
  (Polychromatic418967fa.accept_10_5_3_2_1_899 35 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 153 192 (Polychromatic418967fa.accept_18_16_9_12_1_1182 34 153 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 153 192 3 11 51 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 153 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 153 192 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 153 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 153 192 3 10 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 192
  (Polychromatic418967fa.accept_18_11_9_12_1_4427 29 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 153 192 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 153 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 192 3 9 51 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 192
  (Polychromatic418967fa.accept_11_4_10_5_1_1202 26 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 153 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 153 192 3 8 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 153 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 192
  (Polychromatic418967fa.accept_15_7_3_12_1_365 22 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 153 192 3 7 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 153 192 (Polychromatic418967fa.accept_21_20_6_3_1_9691 20 153 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 192 (Polychromatic418967fa.accept_20_19_13_12_1_2476 19
  153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 192 3 6 51 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 192
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 153 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 153 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 153 192 3 5 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 153 192
  (Polychromatic418967fa.accept_19_14_1_2_1_11172 14 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 153 192 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 153 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 192 3 4 51 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 192 (Polychromatic418967fa.accept_18_10_9_12_1_3259 10 153 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 192 3 3 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 192 (Polychromatic418967fa.accept_15_8_3_12_1_1657
  8 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 192
  (Polychromatic418967fa.accept_15_7_3_12_1_365 7 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 153 192 3 2 51 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 192 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 153 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 153 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 192 3 1 51 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 153 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 192 (Polychromatic418967fa.accept_10_1_3_2_1_220 1 153 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 192)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 152 192
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 152 192 8 5 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 152 192 (Polychromatic418967fa.accept_18_3_8_12_1_3283 39 152 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 152 192 2 19 76 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 152 192 (accept_3_4 37 152 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 152 192 4 9 38 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 152 192
  (Polychromatic418967fa.accept_15_5_2_12_1_2543 35 152 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 152 192 2 17 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 152 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 152 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 152 192 8 4 19 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 152 192 (accept_3_4 31 152 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 152 192 2 15 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 152 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 29
  152 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 192 4 7 38 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 192
  (Polychromatic418967fa.accept_13_1_9_10_1_625 27 152 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 192 2 13 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 192 (accept_3_4 25 152 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 192 8 3 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 152 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 152 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 192 2 11 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 192 (Polychromatic418967fa.accept_15_6_2_12_1_885
  21 152 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 152 192 4 5 38 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 152 192
  (accept_3_4 19 152 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 152 192 2 9 76 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 152 192
  (Polychromatic418967fa.accept_23_17_14_8_1_11171 17 152 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 152 192 8 2 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 152 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 152 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 192 2 7 76 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 192 (accept_3_4 13 152 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 192 4 3 38 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 152 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 152 192 2 5 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 152 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 152 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 152 192 8 1 19 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 152 192 (accept_3_4 7 152 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 152 192 2 3 76 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 152 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 152 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 152 192 4 1 38 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 152 192 (Polychromatic418967fa.accept_15_3_2_12_1_2469
  3 152 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 192 2 1 76 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 192 (accept_3_4 1
  152 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152 192)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 151 192 (Eq.refl Bool.true) (allA_succ_of_accept 41 151 192 (accept_3_5 41 151 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 151 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 151 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 151 192
  (Polychromatic418967fa.accept_10_9_1_2_1_522 39 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 151 192 (accept_3_5 38 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 151 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 151 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 151 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 151 192 (accept_3_5 35 151 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 151 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 151 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 151 192
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 151 192 (accept_3_5 32 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 151 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 151 192 (Polychromatic418967fa.accept_13_4_8_10_1_671 30 151 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 192 (accept_3_5 29 151 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 151 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 151 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 27 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 151 192 (accept_3_5 26 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 151 192 (Polychromatic418967fa.accept_11_3_8_5_1_336 25 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 151 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 151 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 192 (accept_3_5 23 151 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 151 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 151 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 192
  (Polychromatic418967fa.accept_14_7_11_10_1_2155 21 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 151 192 (accept_3_5 20 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 151 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 151 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 151 192 (Polychromatic418967fa.accept_13_5_8_10_1_4363 18 151
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 192 (accept_3_5 17 151
  192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 151 192
  (Polychromatic418967fa.accept_10_6_1_2_1_874 16 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 151 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 151 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 192 (accept_3_5 14 151 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 151 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 151 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 151 192
  (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 151 192 (accept_3_5 11 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 151 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 151 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 151 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 192 (accept_3_5 8 151 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 192 (Polychromatic418967fa.accept_13_7_8_10_1_2663
  7 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 151 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 151 192 (accept_3_5 5 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  151 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 151 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 151 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 151 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 192 (accept_3_5 2 151 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 151 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151 192))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 150 192 (Eq.refl Bool.true) (allA_succ_of_gcd 42 150 192 6 7 25 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 150 192
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 150 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 150 192 2 20 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 150 192 3 13 50 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 150 192 2 19 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 150 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 150 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 150 192 6 6 25 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 150 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 150 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 150 192 2 17 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 150 192 3 11 50 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 150 192 2 16 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 150 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 150 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 192 6 5 25 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 192
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 150 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 150 192 2 14 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 150 192 3 9 50 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 150 192 2 13 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 150 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 150 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 192 6 4 25 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 192
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 150 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 150 192 2 11 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 150 192 3 7 50 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 150 192 2 10 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 150 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 150 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 150 192 6 3 25 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 150 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 150 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 150 192 2 8 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 150 192 3 5 50 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 150 192 2 7 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 150 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 150 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 192 6 2 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  150 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 192 2 5 75 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 150 192 3 3 50 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 150 192 2 4 75 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 150 192
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 150 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 150 192 6 1 25 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 150 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 150 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 150 192 2 2 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 150 192 3 1 50 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 150 192 2 1 75 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 150 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  192))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 149 192 (Eq.refl Bool.true) (allA_succ_of_accept 43 149
  192 (accept_3_4 43 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 192
  (Polychromatic418967fa.accept_9_6_5_3_1_205 42 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 149 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 149 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 192 (accept_3_4 40 149 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 149 192 (Polychromatic418967fa.accept_15_9_14_12_1_913 39 149 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 192 (accept_3_4 37 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 149 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 192 (accept_3_4 34 149 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 149 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 192
  (Polychromatic418967fa.accept_11_10_6_5_1_1239 32 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 192 (accept_3_4 31 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 192 (Polychromatic418967fa.accept_13_4_6_10_1_1199 30 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 149 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 192 (accept_3_4 28 149 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 149 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 192 (accept_3_4 25 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 192 (Polychromatic418967fa.accept_11_1_6_5_1_1732 23 149 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 192 (accept_3_4 22 149 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 149 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 192
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 192 (accept_3_4 19 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 192 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 149 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 192 (accept_3_4 16 149 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 149 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 192
  (Polychromatic418967fa.accept_19_14_16_2_1_6952 14 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 149 192 (accept_3_4 13 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 149 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 149 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 149 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 192 (accept_3_4 10 149 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 192 (Polychromatic418967fa.accept_13_9_6_10_1_666
  9 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 192 (accept_3_4 7 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 149 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 192 (accept_3_4 4 149 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 192 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 149 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 192 (accept_3_4 1 149 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  192)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 148 192 (Eq.refl Bool.true) (allA_succ_of_gcd 44 148
  192 4 11 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43
  148 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 148 192 2 21 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 148 192 (accept_3_5 41 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 148 192 4 10 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 148 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 148 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 148 192 2 19 74 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 148 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 148 192 4 9 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 192 (accept_3_5 35 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  148 192 2 17 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 148 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 148 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 148 192 4 8 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 148 192 (Polychromatic418967fa.accept_15_1_13_12_1_347
  31 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 148 192 2 15 74 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 148 192
  (accept_3_5 29 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 148 192 4 7 37 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 148 192
  (Polychromatic418967fa.accept_17_10_12_5_1_6028 27 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 148 192 2 13 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 148 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 148 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 148 192 4 6 37 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 148 192 (accept_3_5 23 148 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 148 192 2 11 74 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 148 192
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 21 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 148 192 4 5 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 148 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 148 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 148 192 2 9 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 148 192 (accept_3_5 17 148 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 148 192 4 4 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 148 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 148 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 148 192 2 7 74 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 148 192
  (Polychromatic418967fa.accept_19_13_15_2_1_4126 13 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 148 192 4 3 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 148 192 (accept_3_5 11 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 148 192 2 5 74 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 148 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 148 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 148 192 4 2 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 148 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 148 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 148 192 2 3 74 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 148 192 (accept_3_5 5 148 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 148 192 4 1 37 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 148 192 (Polychromatic418967fa.accept_15_3_13_12_1_348
  3 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 148 192 2 1 74 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 148 192
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 148 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 148 192))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 147 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 147 192 3 15 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 147 192 (Polychromatic418967fa.accept_10_4_7_2_1_211 44 147 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 192 (Polychromatic418967fa.accept_11_10_4_5_1_359
  43 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 147 192 3 14 49 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 147 192
  (Polychromatic418967fa.accept_17_7_11_5_1_3539 41 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 192 (Polychromatic418967fa.accept_13_1_4_10_1_622 40 147 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 147 192 3 13 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 147 192 (Polychromatic418967fa.accept_18_2_3_12_1_1155
  38 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 192
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 147 192 3 12 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 147 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 147 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 192
  (Polychromatic418967fa.accept_10_4_7_2_1_211 34 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 192 3 11 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 192 (Polychromatic418967fa.accept_11_10_4_5_1_359 32 147 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 192
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 147 192 3 10 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 147 192 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 147 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 192
  (Polychromatic418967fa.accept_25_3_22_17_1_11170 28 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 147 192 3 9 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 147 192 (Polychromatic418967fa.accept_18_8_3_12_1_3247 26 147 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 192
  (Polychromatic418967fa.accept_10_5_7_2_1_516 25 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 147 192 3 8 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 147 192 (Polychromatic418967fa.accept_17_6_11_5_1_3506 23 147 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 192 (Polychromatic418967fa.accept_20_2_7_12_1_5215 22 147
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 147 192 3 7 49 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 147 192
  (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 147 192 (Polychromatic418967fa.accept_10_9_7_2_1_887 19 147 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 192 3 6 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 192 (Polychromatic418967fa.accept_14_3_7_10_1_2146
  17 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 147 192
  (Polychromatic418967fa.accept_17_16_11_5_1_9843 16 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 147 192 3 5 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 147 192 (Polychromatic418967fa.accept_10_4_7_2_1_211 14 147 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 192
  (Polychromatic418967fa.accept_18_13_3_12_1_3207 13 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 147 192 3 4 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 147 192 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 147 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 192
  (Polychromatic418967fa.accept_11_10_4_5_1_359 10 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 147 192 3 3 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 147 192 (Polychromatic418967fa.accept_13_8_4_10_1_4358 8 147 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 192 (Polychromatic418967fa.accept_13_7_4_10_1_2675 7 147
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 192 3 2 49 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 192
  (Polychromatic418967fa.accept_10_5_7_2_1_516 5 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 192 (Polychromatic418967fa.accept_10_4_7_2_1_211 4 147 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 147 192 3 1 49 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 147 192 (Polychromatic418967fa.accept_18_2_3_12_1_1155 2 147 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 192
  (Polychromatic418967fa.accept_13_1_4_10_1_622 1 147 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 147 192)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 146 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 46 146 192 2 23 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 146 192 (Polychromatic418967fa.accept_13_6_3_10_1_698 45 146 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 146 192 2 22 73 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 146 192 (accept_3_4 43 146 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 146 192 2 21 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 146 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 146 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 146 192 2 20 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 146 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 146 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 146 192 2 19 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 146 192 (accept_3_4 37 146 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 146 192 2 18 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 146 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 35
  146 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 192 2 17 73 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 192
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 146 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 192 2 16 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 192 (accept_3_4 31 146 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 192 2 15 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 192 (Polychromatic418967fa.accept_15_14_11_12_1_4440 29 146 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 192 2 14 73 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 192
  (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 146 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 192 2 13 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 192 (accept_3_4 25 146 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 192 2 12 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 146 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 192 2 11 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 192
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 146 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 192 2 10 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 192 (accept_3_4 19 146 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 192 2 9 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 146 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 146 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 192 2 8 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 15
  146 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 146 192 2 7 73 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 146 192 (accept_3_4 13
  146 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 146 192 2 6 73 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 146 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 146 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 146 192 2 5 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 146 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 146 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 146 192 2 4 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 146 192 (accept_3_4 7 146 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 146 192 2 3 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 146 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 146 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 146 192 2 2 73 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 146 192 (Polychromatic418967fa.accept_14_3_6_10_1_752 3
  146 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 192 2 1 73 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 192 (accept_3_4 1
  146 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146 192)))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 48 145 192 (Eq.refl Bool.true) (allA_succ_of_accept 47 145 192 (accept_3_5 47 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 145 192 (Polychromatic418967fa.accept_17_12_9_5_1_799 46 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 145 192
  (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 145 192 (accept_3_5 44 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 145 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 43 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 145 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 145 192 (accept_3_5 41 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 145 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 145 192
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 145 192 (accept_3_5 38 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 145 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 145 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 145 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 145 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 192 (accept_3_5 35 145 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 145 192 (Polychromatic418967fa.accept_9_7_1_3_1_443
  34 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 145 192 (accept_3_5 32 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 145 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 145 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 192 (accept_3_5 29 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 145 192 (Polychromatic418967fa.accept_10_8_5_2_1_881 28 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 192
  (Polychromatic418967fa.accept_10_7_5_2_1_880 27 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 145 192 (accept_3_5 26 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 145 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 145 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 192 (accept_3_5 23 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 145 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 192
  (Polychromatic418967fa.accept_13_8_2_10_1_652 21 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 145 192 (accept_3_5 20 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 145 192 (Polychromatic418967fa.accept_11_8_2_5_1_1769 19 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 145 192 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 192 (accept_3_5 17 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 145 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 145 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 145 192 (accept_3_5 14 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 145 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 145 192 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 192 (accept_3_5 11 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 145 192 (Polychromatic418967fa.accept_19_10_12_2_1_6948 10 145
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 145 192 (accept_3_5 8 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  145 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 145 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 192 (accept_3_5 5 145 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 145 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 145 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 192
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 145 192 (accept_3_5 2 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  145 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 145 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 145 192)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 144 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 144 192 48 1 3 4 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 144 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 192 2 23 72 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 144 192 3 15 48 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 144 192 4 11 36 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 144 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 192 6 7 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 144 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 144 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 192 8 5 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 144 192 3 13 48 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 144 192 2 19 72 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 144 192
  (Polychromatic418967fa.accept_10_7_4_2_1_903 37 144 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 192 12 3 12 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 192 (Polychromatic418967fa.accept_13_9_1_10_1_647 35 144 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 192 2 17 72 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 144 192 3 11 48 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 144 192 16 2 9 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 144 192
  (Polychromatic418967fa.accept_21_10_18_3_1_11147 31 144 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 144 192 6 5 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 144 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 144 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 192 4 7 36 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 144 192 3 9 48 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 144 192 2 13 72 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 192
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 25 144 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 144 192 24 1 6 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 192 (Polychromatic418967fa.accept_19_4_11_2_1_11111 23 144 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 192 2 11 72 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 144 192 3 7 48 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 144 192 4 5 36 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 192
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 19 144 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 192 6 3 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 144 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 144 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 192 16 1 9 12 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 144 192 3 5 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 144 192 2 7 72 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 13
  144 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 192 12 1 12 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 192
  (Polychromatic418967fa.accept_13_11_1_10_1_648 11 144 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 144 192 2 5 72 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 144 192 3 3 48 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 144 192 8 1 18 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 144 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 192 6 1 24 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 192 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 144 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 144 192 4 1 36 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 144 192 3 1 48 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 144 192 2 1 72 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 1 144 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 144 192))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 143 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 49 143 192 (accept_3_4 49 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 192 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 192 (accept_3_4 46 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 192 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 143 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 192
  (Polychromatic418967fa.accept_19_6_10_2_1_6874 44 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 192 (accept_3_4 43 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 192 (accept_3_4 40 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 192 (Polychromatic418967fa.accept_21_18_17_3_1_4906 39 143 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 192 (accept_3_4 37 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 192 (Polychromatic418967fa.accept_19_17_10_2_1_9793 36 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 192 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 143 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 192 (accept_3_4 34 143 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 143 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 192
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 192 (accept_3_4 31 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 192 (Polychromatic418967fa.accept_19_11_10_2_1_9757 30 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 192 (accept_3_4 28 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 192 (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 143 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 192
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 26 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 143 192 (accept_3_4 25 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 143 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 143 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 143 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 192 (accept_3_4 22 143 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 192 (Polychromatic418967fa.accept_10_1_3_2_1_220
  21 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 192 (accept_3_4 19 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 192 (Polychromatic418967fa.accept_15_3_8_12_1_900 18 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 192 (Polychromatic418967fa.accept_19_17_10_2_1_9793 17 143 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 192 (accept_3_4 16 143 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 143 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 192
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 192 (accept_3_4 13 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 192 (Polychromatic418967fa.accept_17_12_7_5_1_8659 12 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 192 (accept_3_4 10 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 192 (Polychromatic418967fa.accept_17_9_7_5_1_1566 9 143 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 192
  (Polychromatic418967fa.accept_19_8_10_2_1_5414 8 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 192 (accept_3_4 7 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 192 (accept_3_4 4 143 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 192 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 143 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 192 (accept_3_4 1 143 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  192)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 142 192 (Eq.refl Bool.true) (allA_succ_of_gcd 50
  142 192 2 25 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 49 142 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 142 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 142 192 2 24 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 142 192 (accept_3_5 47 142 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 46 142 192 2 23 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 142 192 (Polychromatic418967fa.accept_13_6_12_10_1_690 45 142
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 142 192 2 22 71 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 142 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 43 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 142 192 2 21 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 192 (accept_3_5 41 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 142 192 2 20 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 142 192 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 142 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 142 192 2 19 71 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 142 192
  (Polychromatic418967fa.accept_9_1_7_3_1_41 37 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 142 192 2 18 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 142 192 (accept_3_5 35 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 142 192 2 17 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 142 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 142 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 142 192 2 16 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 142 192
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 142 192 2 15 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 142 192 (accept_3_5 29 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 142 192 2 14 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 142 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 142 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 142 192 2 13 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 142 192
  (Polychromatic418967fa.accept_15_10_7_12_1_2490 25 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 142 192 2 12 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 142 192 (accept_3_5 23 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 142 192 2 11 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 142 192 (Polychromatic418967fa.accept_13_8_12_10_1_4414 21 142 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 142 192 2 10 71 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 142 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 142 192 2 9 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 142 192 (accept_3_5 17 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  142 192 2 8 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 142 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 142 192 2 7 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 142 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 142 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 142 192 2 6 71 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 142 192 (accept_3_5 11 142 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 142 192 2 5 71 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 142 192
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 142 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 142 192 2 4 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 142 192 (Polychromatic418967fa.accept_13_7_12_10_1_640 7 142 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 142 192 2 3 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 142 192 (accept_3_5 5 142 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 142 192 2 2 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 142 192 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 142 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 142 192 2 1 71 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 142 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 1
  142 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142
  192))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 141 192 (Eq.refl Bool.true) (allA_succ_of_gcd 51
  141 192 3 17 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 50 141 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 141 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 141 192 3 16 47 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 141 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 141 192 3 15 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 141 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 44
  141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 192
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 141 192 3 14 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 141 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 141 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 192 (Polychromatic418967fa.accept_7_5_1_3_1_103
  40 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 192 3 13 47 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 192
  (Polychromatic418967fa.accept_9_2_6_3_1_178 38 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 141 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 141 192 3 12 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 141 192 (Polychromatic418967fa.accept_9_8_6_3_1_457 35
  141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 192
  (Polychromatic418967fa.accept_9_7_6_3_1_456 34 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 141 192 3 11 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 141 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 141 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 192 (Polychromatic418967fa.accept_9_4_6_3_1_179
  31 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 192 3 10 47 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 192
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 28 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 141 192 3 9 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 141 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 26
  141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 141 192 3 8 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 141 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 141 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 192 3 7 47 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 192
  (Polychromatic418967fa.accept_9_2_6_3_1_178 20 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 141 192 3 6 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 141 192 (Polychromatic418967fa.accept_9_8_6_3_1_457 17
  141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 16 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 141 192 3 5 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 141 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 141 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 192 3 4 47 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 141 192 3 3 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 141 192 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 141 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 192
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 141 192 3 2 47 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 141 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 141 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 192 3 1 47 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 2 141 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 141 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 141 192)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53
  140 192 (Eq.refl Bool.true) (allA_succ_of_gcd 52 140 192 4 13 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 140 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 140 192 2 25 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 140 192 (accept_3_4 49
  140 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 140 192 4 12 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 140 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 140 192 2 23 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 140 192 (Polychromatic418967fa.accept_25_20_15_17_1_11169 45 140 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 140 192 4 11 35 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 140 192 (accept_3_4 43 140 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 140 192 2 21 70 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 140 192
  (Polychromatic418967fa.accept_22_19_8_16_1_3106 41 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 140 192 4 10 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 140 192 (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 140 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 140 192 2 19 70 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 140 192 (accept_3_4 37 140 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 140 192 4 9 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 140 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 140 192 2 17 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 140 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 140 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 192 4 8 35 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 192 (accept_3_4 31 140 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 192 2 15 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 29
  140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 192 4 7 35 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 192
  (Polychromatic418967fa.accept_21_6_14_3_1_4932 27 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 192 2 13 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 192 (accept_3_4 25 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 192 4 6 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 140 192 (Polychromatic418967fa.accept_15_8_5_12_1_4453 23 140 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 192 2 11 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 192 (Polychromatic418967fa.accept_15_6_5_12_1_1642
  21 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 140 192 4 5 35 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 140 192
  (accept_3_4 19 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 140 192 2 9 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 140 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 140 192 4 4 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 140 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 140 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 192 2 7 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 192 (accept_3_4 13 140 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 192 4 3 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 140 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 192 2 5 70 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 192
  (Polychromatic418967fa.accept_15_9_5_12_1_1640 9 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 192 4 2 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 192 (accept_3_4 7 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  192 2 3 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 192 (Polychromatic418967fa.accept_19_5_7_2_1_1728 5 140 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 192 4 1 35 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 140 192 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 140 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 192 2 1 70 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 192 (accept_3_4 1 140 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 140 192))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 139 192
  (Eq.refl Bool.true) (allA_succ_of_accept 53 139 192 (accept_3_5 53 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 139 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 139 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 139 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 139 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 139 192 (accept_3_5 50 139 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 139 192
  (Polychromatic418967fa.accept_20_9_19_12_1_5221 49 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 139 192 (Polychromatic418967fa.accept_19_10_6_2_1_6907 48 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 139 192 (accept_3_5 47 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 139 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 46 139 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 139 192
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 45 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 139 192 (accept_3_5 44 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 192 (accept_3_5 41 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 192 (Polychromatic418967fa.accept_13_1_9_10_1_625 40 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 39 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 139 192 (accept_3_5 38 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 139 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 139 192 (Polychromatic418967fa.accept_17_2_3_5_1_763 36 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 192 (accept_3_5 35 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 139 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 192 (accept_3_5 32 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 31 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 192 (accept_3_5 29 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 192
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 139 192 (accept_3_5 26 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 139 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 139 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 192 (accept_3_5 23 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 192 (Polychromatic418967fa.accept_15_7_4_12_1_2530 22 139 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 192
  (Polychromatic418967fa.accept_10_1_9_2_1_45 21 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 192 (accept_3_5 20 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 192 (accept_3_5 17 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 192 (accept_3_5 14 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 192 (Polychromatic418967fa.accept_19_13_6_2_1_4124 13 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 192 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 192 (accept_3_5 11 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 139 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 192 (accept_3_5 8 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 192 (accept_3_5 5 139 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 4 139 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 192
  (Polychromatic418967fa.accept_14_3_13_10_1_761 3 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 192 (accept_3_5 2 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 139 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 192)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 138 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 54 138 192 6 9 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 192 (Polychromatic418967fa.accept_15_8_3_12_1_1657 53 138 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 192 2 26 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 138 192 3 17 46 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 138 192 2 25 69 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 138 192
  (Polychromatic418967fa.accept_21_7_12_3_1_4849 49 138 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 192 6 8 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 138 192 (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 138 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 192 2 23 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 138 192 3 15 46 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 138 192 2 22 69 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 138 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 138 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 192 6 7 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 138 192 (Polychromatic418967fa.accept_13_2_8_10_1_1902 41 138 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 192 2 20 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 138 192 3 13 46 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 138 192 2 19 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 138 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 138 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 192 6 6 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 138 192 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 138 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 192 2 17 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 138 192 3 11 46 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 138 192 2 16 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 138 192
  (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 138 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 192 6 5 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 138 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 138 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 192 2 14 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 138 192 3 9 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 138 192 2 13 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 138 192
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 138 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 192 6 4 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 138 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 138 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 192 2 11 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 138 192 3 7 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 138 192 2 10 69 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 138 192
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 19 138 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 138 192 6 3 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 138 192 (Polychromatic418967fa.accept_13_4_8_10_1_671 17 138 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 192 2 8 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 138 192 3 5 46 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 138 192 2 7 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 138 192
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 138 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 138 192 6 2 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 138 192 (Polychromatic418967fa.accept_13_11_8_10_1_676 11 138 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 192 2 5 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 138 192 3 3 46 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 138 192 2 4 69 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 138 192
  (Polychromatic418967fa.accept_13_7_8_10_1_2663 7 138 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 138 192 6 1 23 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 138 192 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 138 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 138 192 2 2 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 138 192 3 1 46 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 138 192 2 1 69 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 138 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 56 137 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 55 137 192 (accept_3_4 55 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 192 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 192 (accept_3_4 52 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 50 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 192 (accept_3_4 49 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 48 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 192 (Polychromatic418967fa.accept_13_8_7_10_1_4362 47 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 192 (accept_3_4 46 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 137
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 192 (accept_3_4 43 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 192 (accept_3_4 40 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 192 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 192
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 38 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 137 192 (accept_3_4 37 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 137 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 36 137 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 137 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 192 (accept_3_4 34 137 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 192 (Polychromatic418967fa.accept_9_6_2_3_1_771
  33 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 192 (accept_3_4 31 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 192 (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 192 (accept_3_4 28 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 192 (accept_3_4 25 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 192 (accept_3_4 22 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 192 (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 137 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 20 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 192 (accept_3_4 19 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 192 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 192 (accept_3_4 16 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 192 (accept_3_4 13 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 192 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 192 (Polychromatic418967fa.accept_19_11_4_2_1_1700 11 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 192 (accept_3_4 10 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 192 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 137 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 192 (accept_3_4 7 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 6 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 192 (accept_3_4 4 137 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 192 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 137 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 192
  (Polychromatic418967fa.accept_20_2_17_12_1_5178 2 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 192 (accept_3_4 1 137 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 57 136 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 56 136 192 8 7 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 136 192 (Polychromatic418967fa.accept_13_3_6_10_1_2658 55 136 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 136 192 2 27 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 136 192 (accept_3_5 53 136 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 52 136 192 4 13 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 136 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 136 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 136 192 2 25 68 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 136 192
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 136 192 8 6 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 136 192 (accept_3_5 47 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  136 192 2 23 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 136 192 (Polychromatic418967fa.accept_18_9_10_12_1_5793 45 136 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 136 192 4 11 34 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 136 192
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 136 192 2 21 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 136 192 (accept_3_5 41 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 136 192 8 5 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 136 192 (Polychromatic418967fa.accept_19_1_3_2_1_11168 39 136 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 136 192 2 19 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 136 192 (Polychromatic418967fa.accept_19_18_3_2_1_6939
  37 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 136 192 4 9 34 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 136 192
  (accept_3_5 35 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 136 192 2 17 68 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 136 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 33 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 136 192 8 4 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 136 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 136 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 136 192 2 15 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 136 192 (accept_3_5 29 136 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 136 192 4 7 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 136 192 (Polychromatic418967fa.accept_18_9_10_12_1_5793 27 136
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 136 192 2 13 68 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 136 192
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 136 192 8 3 17 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 136 192 (accept_3_5 23 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  136 192 2 11 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 136 192 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 136 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 136 192 4 5 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 136 192 (Polychromatic418967fa.accept_15_4_1_12_1_914
  19 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 136 192 2 9 68 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 136 192
  (accept_3_5 17 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 136 192 8 2 17 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 136 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 136 192 2 7 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 136 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 136 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 136 192 4 3 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 136 192 (accept_3_5 11 136 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 136 192 2 5 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 136 192 (Polychromatic418967fa.accept_13_9_6_10_1_666 9 136 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 136 192 8 1 17 24 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 136 192
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 136 192 2 3 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 136 192 (accept_3_5 5 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 136
  192 4 1 34 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  136 192 (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 136 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 136 192 2 1 68 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 136 192 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 136 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 136 192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 135 192 (Eq.refl Bool.true) (allA_succ_of_gcd 57 135 192 3 19 45 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 135 192
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 56 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 135 192 3 18 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 135 192 (Polychromatic418967fa.accept_10_3_5_2_1_38 53
  135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 192
  (Polychromatic418967fa.accept_11_8_3_5_1_355 52 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 135 192 3 17 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 135 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 50 135 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 192 (Polychromatic418967fa.accept_21_7_9_3_1_8059
  49 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 135 192 3 16 45 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 135 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 192 (Polychromatic418967fa.accept_18_10_9_12_1_3259 46 135 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 135 192 3 15 45 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 135 192
  (Polychromatic418967fa.accept_21_2_9_3_1_4841 44 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 135 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 135 192 3 14 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 135 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 40 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 135 192 3 13 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 135 192 (Polychromatic418967fa.accept_10_8_5_2_1_881 38 135 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 192 (Polychromatic418967fa.accept_10_7_5_2_1_880
  37 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 135 192 3 12 45 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 135 192
  (Polychromatic418967fa.accept_17_1_16_5_1_3670 35 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 135 192 3 11 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 135 192 (Polychromatic418967fa.accept_13_6_5_10_1_1213
  32 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 192
  (Polychromatic418967fa.accept_21_10_9_3_1_11127 31 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 135 192 3 10 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 135 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 135 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 192
  (Polychromatic418967fa.accept_10_8_5_2_1_881 28 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 192 3 9 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 26 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 192 (Polychromatic418967fa.accept_20_5_15_12_1_9720 25 135
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 192 3 8 45 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 192
  (Polychromatic418967fa.accept_10_3_5_2_1_38 23 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 192 3 7 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 20
  135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 19 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 135 192 3 6 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 135 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 192 (Polychromatic418967fa.accept_18_16_9_12_1_1182 16 135
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 135 192 3 5 45 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 135 192
  (Polychromatic418967fa.accept_21_14_9_3_1_4893 14 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 192 3 4 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 192
  (Polychromatic418967fa.accept_17_11_16_5_1_3612 11 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 135 192 (Polychromatic418967fa.accept_18_10_9_12_1_3259 10 135 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 192 3 3 45 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 135 192 3 2 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 135 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 135 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 192
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 4 135 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 135 192 3 1 45 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 135 192 (Polychromatic418967fa.accept_13_2_5_10_1_250 2 135 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 135 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 134 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 58 134 192 2 29 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 134 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 57 134 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 134 192 2 28 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 134 192 (accept_3_4 55 134 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 134 192 2 27 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 134 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 53
  134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 192 2 26 67 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 51 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 192 2 25 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 192 (accept_3_4 49 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 192 2 24 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 134 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 192 2 23 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 192
  (Polychromatic418967fa.accept_13_6_4_10_1_660 45 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 192 2 22 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 192 (accept_3_4 43 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 192 2 21 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 134 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 192 2 20 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 39 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 192 2 19 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 192 (accept_3_4 37 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 192 2 18 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 192 (Polychromatic418967fa.accept_21_14_8_3_1_8085 35 134 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 192 2 17 67 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 33 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 192 2 16 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 192 (accept_3_4 31 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 192 2 15 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 134 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 192 2 14 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 192
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 192 2 13 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 192 (accept_3_4 25 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 192 2 12 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 134 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 192 2 11 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 192
  (Polychromatic418967fa.accept_13_8_4_10_1_4358 21 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 192 2 10 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 192 (accept_3_4 19 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 192 2 9 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 134 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 134 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 192 2 8 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 15
  134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 134 192 2 7 67 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 134 192 (accept_3_4 13
  134 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 134 192 2 6 67 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 134 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 134 192 2 5 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 134 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 134 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 134 192 2 4 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 134 192 (accept_3_4 7 134 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 134 192 2 3 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 134 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 134 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 134 192 2 2 67 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 134 192 (Polychromatic418967fa.accept_18_3_8_12_1_3283
  3 134 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 192 2 1 67 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 192 (accept_3_4 1
  134 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 133 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 59 133 192 (accept_3_5 59 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 133 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 133 192 (Polychromatic418967fa.accept_18_3_7_12_1_1196 57 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 133 192 (accept_3_5 56 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 133 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 133 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 133 192
  (Polychromatic418967fa.accept_13_2_3_10_1_658 54 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 133 192 (accept_3_5 53 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 133 192 (Polychromatic418967fa.accept_21_10_7_3_1_4884 52 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 133 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 133 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 133 192 (accept_3_5 50 133 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 133 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 192
  (Polychromatic418967fa.accept_15_3_13_12_1_348 48 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 133 192 (accept_3_5 47 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 133 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 133 192 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 133 192 (accept_3_5 44 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 133 192 (Polychromatic418967fa.accept_17_9_14_5_1_1555 43 133
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 133 192
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 133 192 (accept_3_5 41 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 133 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 133 192 (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 133 192 (accept_3_5 38 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 133 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 133 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 133 192
  (Polychromatic418967fa.accept_17_2_14_5_1_2575 36 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 133 192 (accept_3_5 35 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 133 192 (Polychromatic418967fa.accept_22_12_1_16_1_3122 34 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 133 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 133 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 133 192 (accept_3_5 32 133 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 133 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 133 192
  (Polychromatic418967fa.accept_20_10_13_12_1_9726 30 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 133 192 (accept_3_5 29 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 133 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 133 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 192 (Polychromatic418967fa.accept_17_10_14_5_1_11167 27
  133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 133 192 (accept_3_5 26
  133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 133 192
  (Polychromatic418967fa.accept_10_5_3_2_1_899 25 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 133 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 133 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 192 (accept_3_5 23 133 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 133 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 133 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 192 (Polychromatic418967fa.accept_10_1_3_2_1_220
  21 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 133 192 (accept_3_5 20
  133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 133 192
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 133 192 (Polychromatic418967fa.accept_14_4_7_10_1_3888 18 133 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 192 (accept_3_5 17 133 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 133 192 (Polychromatic418967fa.accept_15_1_13_12_1_347 16 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 192
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 192 (accept_3_5 14 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 192 (Polychromatic418967fa.accept_21_12_7_3_1_4927 12 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 192 (accept_3_5 11 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 133 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 192
  (Polychromatic418967fa.accept_17_9_14_5_1_1555 9 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 192 (accept_3_5 8 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 192 (Polychromatic418967fa.accept_13_7_3_10_1_656 7 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 133 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 192 (accept_3_5 5 133 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 133 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 192
  (Polychromatic418967fa.accept_14_3_7_10_1_2146 3 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 192 (accept_3_5 2 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 133 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 132 192
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 132 192 12 5 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 132 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 59 132 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 192 2 29 66 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 132 192 3 19 44 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 132 192 4 14 33
  48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 132 192
  (Polychromatic418967fa.accept_9_1_6_3_1_177 55 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 192 6 9 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 132 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 132 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 192 4 13 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 132 192 3 17 44 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 132 192 2 25 66 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 132 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 192 12 4 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 132 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 192 2 23 66 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 132 192 3 15 44 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 132 192 4 11 33 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 132 192
  (Polychromatic418967fa.accept_9_7_6_3_1_456 43 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 192 6 7 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 132 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 132 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 192 4 10 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 132 192 3 13 44 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 132 192 2 19 66 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 132 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 192 12 3 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 192 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 132 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 192 2 17 66 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 132 192 3 11 44 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 132 192 4 8 33 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 192 6 5 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 132 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 132 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 192 4 7 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 132 192 3 9 44 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 132 192 2 13 66 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 192 12 2 11 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 132 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 192 2 11 66 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 132 192 3 7 44 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 132 192 4 5 33 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 132 192
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 192 6 3 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 192 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 132 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 192 4 4 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 132 192 3 5 44 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 132 192 2 7 66 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 132 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 13
  132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 132 192 12 1 11 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 132 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 132 192 2 5 66 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 132 192 3 3 44 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 8 132 192 4 2 33 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 132 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 192 6 1 22 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 132 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 132 192 4 1 33 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 132 192 3 1 44 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 132 192 2 1 66 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 192
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 132 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 132 192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 131 192 (Eq.refl
  Bool.true) (allA_succ_of_accept 61 131 192 (accept_3_4 61 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 131 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 131 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 59 131
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 192 (accept_3_4 58 131
  192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 131 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 131 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 192 (accept_3_4 55 131 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 131 192 (Polychromatic418967fa.accept_14_12_5_10_1_2130 54 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 192 (accept_3_4 52 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 192 (accept_3_4 49 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 192 (Polychromatic418967fa.accept_11_4_10_5_1_1202 48 131 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 192 (accept_3_4 46 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 192 (Polychromatic418967fa.accept_18_9_5_12_1_9813 45 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 192 (accept_3_4 43 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 192
  (Polychromatic418967fa.accept_17_7_12_5_1_1580 41 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 192 (accept_3_4 40 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 192 (accept_3_4 37 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 192 (accept_3_4 34 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 192 (Polychromatic418967fa.accept_25_7_6_17_1_11166 32 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 192 (accept_3_4 31 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 131 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 192 (accept_3_4 28 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 192 (Polychromatic418967fa.accept_17_10_12_5_1_6028 27 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 26 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 192 (accept_3_4 25 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 192 (accept_3_4 22 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 192 (Polychromatic418967fa.accept_20_1_11_12_1_2467 21 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 192 (accept_3_4 19 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 192 (Polychromatic418967fa.accept_21_18_5_3_1_11165 18 131 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 192 (accept_3_4 16 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 192 (Polychromatic418967fa.accept_15_14_11_12_1_4440 14 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 192 (accept_3_4 13 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 192 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 131
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 192 (accept_3_4 10 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 8 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 192 (accept_3_4 7 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 131 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 192
  (Polychromatic418967fa.accept_19_5_17_2_1_11164 5 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 192 (accept_3_4 4 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 131 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 192 (accept_3_4 1 131 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63
  130 192 (Eq.refl Bool.true) (allA_succ_of_gcd 62 130 192 2 31 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 130 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 130 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 130 192 2 30 65 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 130 192 (accept_3_5 59
  130 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 130 192 2 29 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 130 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 130 192 2 28 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 130 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 130 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 130 192 2 27 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 130 192 (accept_3_5 53 130 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 130 192 2 26 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 130 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 51
  130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 130 192 2 25 65 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 130 192
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 49 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 130 192 2 24 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 130 192 (accept_3_5 47 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 130 192 2 23 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 130 192 (Polychromatic418967fa.accept_18_9_4_12_1_3209 45 130 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 130 192 2 22 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 130 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 130 192 2 21 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 130 192 (accept_3_5 41 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 130 192 2 20 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 130 192 (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 130 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 130 192 2 19 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 130 192
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 130 192 2 18 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 130 192 (accept_3_5 35 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 130 192 2 17 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 130 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 130 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 130 192 2 16 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 130 192
  (Polychromatic418967fa.accept_36_31_22_12_1_11163 31 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 130 192 2 15 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 130 192 (accept_3_5 29 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 130 192 2 14 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 130 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 130 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 130 192 2 13 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 130 192
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 130 192 2 12 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 130 192 (accept_3_5 23 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 130 192 2 11 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 130 192 (Polychromatic418967fa.accept_14_7_4_10_1_1351 21 130 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 130 192 2 10 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 130 192
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 130 192 2 9 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 130 192 (accept_3_5 17 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  130 192 2 8 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 130 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 130 192 2 7 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 130 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 130 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 130 192 2 6 65 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 130 192 (accept_3_5 11 130 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 130 192 2 5 65 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 130 192
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 130 192 2 4 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 130 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 130 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 130 192 2 3 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 130 192 (accept_3_5 5 130 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 130 192 2 2 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 130 192 (Polychromatic418967fa.accept_19_3_16_2_1_6837 3 130 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 130 192 2 1 65 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 130 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 1
  130 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 129 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 63 129 192 3 21 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 129 192 (Polychromatic418967fa.accept_14_6_3_10_1_3905 62 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 192
  (Polychromatic418967fa.accept_10_1_9_2_1_45 61 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 129 192 3 20 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 129 192 (Polychromatic418967fa.accept_13_7_12_10_1_640 59 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 192
  (Polychromatic418967fa.accept_11_3_8_5_1_336 58 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 129 192 3 19 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 129 192 (Polychromatic418967fa.accept_18_2_3_12_1_1155 56 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 192
  (Polychromatic418967fa.accept_14_13_3_10_1_2159 55 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 129 192 3 18 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 129 192 (Polychromatic418967fa.accept_25_3_4_17_1_11162 53 129 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 192
  (Polychromatic418967fa.accept_22_8_19_16_1_6137 52 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 129 192 3 17 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 129 192 (Polychromatic418967fa.accept_13_11_12_10_1_2652 50 129 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 192
  (Polychromatic418967fa.accept_14_7_3_10_1_1364 49 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 129 192 3 16 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 129 192 (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 192
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 46 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 129 192 3 15 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 129 192 (Polychromatic418967fa.accept_15_14_9_12_1_2498 44 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 192
  (Polychromatic418967fa.accept_18_7_3_12_1_3241 43 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 129 192 3 14 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 129 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 41 129 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 192
  (Polychromatic418967fa.accept_15_10_9_12_1_2497 40 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 129 192 3 13 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 129 192 (Polychromatic418967fa.accept_18_2_3_12_1_1155 38 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 192
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 192 3 12 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 192 (Polychromatic418967fa.accept_11_2_8_5_1_1219 35 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 192
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 34 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 129 192 3 11 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 129 192 (Polychromatic418967fa.accept_13_6_12_10_1_690 32 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 192
  (Polychromatic418967fa.accept_10_1_9_2_1_45 31 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 129 192 3 10 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 129 192 (Polychromatic418967fa.accept_15_14_9_12_1_2498 29 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 192
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 28 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 129 192 3 9 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 129 192 (Polychromatic418967fa.accept_18_8_3_12_1_3247 26 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 192
  (Polychromatic418967fa.accept_11_3_8_5_1_336 25 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 129 192 3 8 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 129 192 (Polychromatic418967fa.accept_20_3_9_12_1_6671 23 129 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 192 (Polychromatic418967fa.accept_13_9_12_10_1_242 22 129
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 192 3 7 43 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 192
  (Polychromatic418967fa.accept_13_7_12_10_1_640 20 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 192 (Polychromatic418967fa.accept_13_6_12_10_1_690 19 129 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 192 3 6 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 192 (Polychromatic418967fa.accept_10_7_9_2_1_1887
  17 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 192
  (Polychromatic418967fa.accept_23_16_14_8_1_11161 16 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 129 192 3 5 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 129 192 (Polychromatic418967fa.accept_11_3_8_5_1_336 14 129 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 192
  (Polychromatic418967fa.accept_11_2_8_5_1_1219 13 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 129 192 3 4 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 129 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 129 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 192 (Polychromatic418967fa.accept_15_10_9_12_1_2497 10 129
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 192 3 3 43 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 192
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 192 (Polychromatic418967fa.accept_10_7_9_2_1_1887 7 129 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 129 192 3 2 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 129 192 (Polychromatic418967fa.accept_15_5_9_12_1_1599 5 129 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 192
  (Polychromatic418967fa.accept_15_4_9_12_1_2495 4 129 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 129 192 3 1 43 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 129 192 (Polychromatic418967fa.accept_11_2_8_5_1_1219 2 129 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 1 129 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65 128 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 64 128 192 64 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 128 192 (Polychromatic418967fa.accept_15_3_8_12_1_900 63 128 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 128 192 2 31 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 128 192 (accept_3_4 61 128 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 128 192 4 15 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 128 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 128 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 192 2 29 64 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 57 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 192 8 7 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 128 192 (accept_3_4 55 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  128 192 2 27 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 128 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 128 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 192 4 13 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 51
  128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 128 192 2 25 64 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 128 192 (accept_3_4 49
  128 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 128 192 16 3 8 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 128 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 128 192 2 23 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 128 192 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 128 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 128 192 4 11 32 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 128 192 (accept_3_4 43 128 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 128 192 2 21 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 128 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 41
  128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 192 8 5 16 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 192
  (Polychromatic418967fa.accept_18_3_2_12_1_5751 39 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 192 2 19 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 192 (accept_3_4 37 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 192 4 9 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 128 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 128 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 192 2 17 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 33
  128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 192 32 1 4 6 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 192 (accept_3_4 31
  128 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 192 2 15 64 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 128 192 4 7 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 128 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 128 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 192 2 13 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 192 (accept_3_4 25 128 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 192 8 3 16 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 128 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 192 2 11 64 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 192
  (Polychromatic418967fa.accept_13_8_11_10_1_636 21 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 192 4 5 32 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 128 192 (accept_3_4 19 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  128 192 2 9 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 128 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 128 192 16 1 8 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 15 128 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 128 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 192 2 7 64 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 192 (accept_3_4 13 128 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 192 4 3 32 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 192
  (Polychromatic418967fa.accept_15_11_8_12_1_4437 11 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 128 192 2 5 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 128 192 (Polychromatic418967fa.accept_11_9_7_5_1_749 9 128 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 128 192 8 1 16 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 128 192 (accept_3_4 7 128 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128 192 2 3 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 128 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 128 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 192 4 1 32 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 192
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 3 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 128 192 2 1 64 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 128 192 (accept_3_4 1 128 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 127 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 127 192 (accept_3_5 65 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 127 192 (Polychromatic418967fa.accept_10_4_7_2_1_211 64 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 127 192 (Polychromatic418967fa.accept_15_3_7_12_1_372 63 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 127 192 (accept_3_5 62 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 127 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 61 127 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 127 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 60 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 127 192 (accept_3_5 59 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 127 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 58 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 127 192 (Polychromatic418967fa.accept_18_3_1_12_1_4419 57 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 127 192 (accept_3_5 56 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 127 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 55 127
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 54 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 192 (accept_3_5 53 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 192 (accept_3_5 50 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 192
  (Polychromatic418967fa.accept_15_3_7_12_1_372 48 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 192 (accept_3_5 47 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 46 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 192 (accept_3_5 44 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 127 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 192 (accept_3_5 41 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 40 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 192 (accept_3_5 38 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 37 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 192
  (Polychromatic418967fa.accept_15_6_7_12_1_869 36 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 192 (accept_3_5 35 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 192 (accept_3_5 32 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 30 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 192 (accept_3_5 29 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 192 (Polychromatic418967fa.accept_21_7_1_3_1_11160 28 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 192 (Polychromatic418967fa.accept_19_8_13_2_1_6921 27 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 192 (accept_3_5 26 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 25 127 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 192 (accept_3_5 23 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 192 (Polychromatic418967fa.accept_11_10_6_5_1_1239 21 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 192 (accept_3_5 20 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 19 127 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 18 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 127 192 (accept_3_5 17 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 127 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 16 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 127 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 192 (accept_3_5 14 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 12 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 192 (accept_3_5 11 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 192 (Polychromatic418967fa.accept_11_10_6_5_1_1239 10 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 192 (accept_3_5 8 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 192 (accept_3_5 5 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 4 127 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 192 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 192 (accept_3_5 2 127 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 192 (Polychromatic418967fa.accept_11_1_6_5_1_1732 1 127 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 126 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 126 192 6 11 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 192 (Polychromatic418967fa.accept_15_5_6_12_1_916 65 126 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 192 2 32 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 126 192 3 21 42 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 126 192 2 31 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 126 192
  (Polychromatic418967fa.accept_10_1_6_2_1_867 61 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 192 6 10 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 192 (Polychromatic418967fa.accept_25_9_1_17_1_11159 59 126 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 192 2 29 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 126 192 3 19 42 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 126 192 2 28 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 126 192
  (Polychromatic418967fa.accept_15_10_6_12_1_1645 55 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 54 126 192 6 9 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 53 126 192 (Polychromatic418967fa.accept_13_1_9_10_1_625 53 126 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 192 2 26 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 126 192 3 17 42 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 126 192 2 25 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 126 192
  (Polychromatic418967fa.accept_17_15_7_5_1_9836 49 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 192 6 8 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 126 192 (Polychromatic418967fa.accept_15_2_6_12_1_1613 47 126 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 192 2 23 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 126 192 3 15 42 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 126 192 2 22 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 126 192
  (Polychromatic418967fa.accept_17_9_7_5_1_1566 43 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 192 6 7 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 126 192 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 126 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 192 2 20 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 126 192 3 13 42 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 126 192 2 19 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 126 192
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 37 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 192 6 6 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 126 192 (Polychromatic418967fa.accept_15_5_6_12_1_916 35 126 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 192 2 17 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 126 192 3 11 42 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 126 192 2 16 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 126 192
  (Polychromatic418967fa.accept_10_1_6_2_1_867 31 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 192 6 5 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 126 192 (Polychromatic418967fa.accept_17_12_7_5_1_8659 29 126 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 192 2 14 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 126 192 3 9 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 126 192 2 13 63 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 126 192
  (Polychromatic418967fa.accept_13_12_9_10_1_1223 25 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 126 192 6 4 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 126 192 (Polychromatic418967fa.accept_19_4_12_2_1_11158 23 126 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 192 2 11 63 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 126 192 3 7 42 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 126 192 2 10 63 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 126 192
  (Polychromatic418967fa.accept_13_6_9_10_1_1201 19 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 192 6 3 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 192 (Polychromatic418967fa.accept_15_2_6_12_1_1613 17 126 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 192 2 8 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 126 192 3 5 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 126 192 2 7 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 126 192
  (Polychromatic418967fa.accept_25_13_1_17_1_7345 13 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 126 192 6 2 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 126 192 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 126 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 192 2 5 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 126 192 3 3 42 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 126 192 2 4 63 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 126 192
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 126 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 126 192 6 1 21 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 126 192 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 126 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 126 192 2 2 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 126 192 3 1 42 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 126 192 2 1 63 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 192 (Polychromatic418967fa.accept_10_1_6_2_1_867 1 126 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 125 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 125 192 (accept_3_4 67 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 192 (Polychromatic418967fa.accept_15_6_5_12_1_1642 66 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 125 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 65 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 125 192 (accept_3_4 64 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 192 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 192
  (Polychromatic418967fa.accept_15_2_5_12_1_369 62 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 192 (accept_3_4 61 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 125 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 60 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 192 (accept_3_4 58 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 192 (accept_3_4 55 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 192 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 192 (accept_3_4 52 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 192
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 192 (accept_3_4 49 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 192 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 192 (accept_3_4 46 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 192 (Polychromatic418967fa.accept_14_3_13_10_1_761 45 125 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 44 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 192 (accept_3_4 43 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 41 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 192 (accept_3_4 40 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 192 (accept_3_4 37 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 192 (Polychromatic418967fa.accept_15_6_5_12_1_1642 36 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 192 (Polychromatic418967fa.accept_17_1_6_5_1_3502 35 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 192 (accept_3_4 34 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 125 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 32 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 192 (accept_3_4 31 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 30 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 29 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 192 (accept_3_4 28 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 192
  (Polychromatic418967fa.accept_20_6_5_12_1_8169 26 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 192 (accept_3_4 25 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 192 (accept_3_4 22 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 192 (Polychromatic418967fa.accept_11_10_4_5_1_359 21 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 192 (accept_3_4 19 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 18 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 192 (accept_3_4 16 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 125 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 192
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 192 (accept_3_4 13 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 192 (Polychromatic418967fa.accept_13_12_8_10_1_1879 12 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 192 (accept_3_4 10 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 192
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 192 (accept_3_4 7 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 192 (accept_3_4 4 125 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 192 (Polychromatic418967fa.accept_10_3_5_2_1_38 3 125 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 2 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 192 (accept_3_4 1 125 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 124 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 124 192 4 17 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 124 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 124 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 124 192 2 33 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 124 192 (accept_3_5 65 124 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 124 192 4 16 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 124 192 (Polychromatic418967fa.accept_11_8_3_5_1_355
  63 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 124 192 2 31 62 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 124 192
  (Polychromatic418967fa.accept_14_5_12_10_1_2985 61 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 124 192 4 15 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 124 192 (accept_3_5 59 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 124 192 2 29 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 124 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 57 124 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 124 192 4 14 31 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 124 192
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 124 192 2 27 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 124 192 (accept_3_5 53 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 124 192 4 13 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 124 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 51 124 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 124 192 2 25 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 124 192
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 124 192 4 12 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 124 192 (accept_3_5 47 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 124 192 2 23 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 124 192 (Polychromatic418967fa.accept_18_9_16_12_1_1143 45 124 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 124 192 4 11 31 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 124 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 124 192 2 21 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 124 192 (accept_3_5 41 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 124 192 4 10 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 124 192 (Polychromatic418967fa.accept_15_9_4_12_1_1611 39 124 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 124 192 2 19 62 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 124 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 124 192 4 9 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 124 192 (accept_3_5 35 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34
  124 192 2 17 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 124 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 124 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 124 192 4 8 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 124 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 31
  124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 124 192 2 15 62 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 124 192 (accept_3_5 29
  124 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 124 192 4 7 31 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 124 192
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 124 192 2 13 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 124 192 (Polychromatic418967fa.accept_13_12_7_10_1_2662 25 124 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 124 192 4 6 31 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 124 192 (accept_3_5 23 124 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 124 192 2 11 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 124 192
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 21 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 124 192 4 5 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 124 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 124 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 124 192 2 9 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 124 192 (accept_3_5 17 124 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 124 192 4 4 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 124 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 15 124 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 124 192 2 7 62 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 124 192
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 124 192 4 3 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 124 192 (accept_3_5 11 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10
  124 192 2 5 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  9 124 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 124 192 4 2 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 124 192 (Polychromatic418967fa.accept_10_7_4_2_1_903 7 124 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 124 192 2 3 62 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 124 192 (accept_3_5 5 124 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 124 192 4 1 31 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 124 192 (Polychromatic418967fa.accept_13_3_7_10_1_668 3 124 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 124 192 2 1 62 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 124 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 1 124 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 124 192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 123 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 123 192 3 23 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 123 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 123 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 123 192 3 22 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 123 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 123 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 123 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 64
  123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 123 192 3 21 41 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 123 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 62 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 123 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 123 192 3 20 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 123 192 3 19 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 123 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 123 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 192 (Polychromatic418967fa.accept_7_6_4_3_1_266
  55 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 123 192 3 18 41 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 123 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 123 192 3 17 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 123 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 50
  123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 123 192 3 16 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 123 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 123 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 123 192 3 15 41 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 123 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 123 192 3 14 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 123 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 41
  123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 192 3 13 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 123 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  37 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 192 3 12 41 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 123 192 3 11 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 123 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 192 3 10 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 123 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 192 3 9 41 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 192 3 8 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 22 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 192 3 7 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 20 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 123 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 192 3 6 41 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 192 3 5 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 192 3 4 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 123 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 192 3 3 41 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 8 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 192 3 2 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 123 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 123 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 192 3 1 41 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 123 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 123 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 122 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 70 122 192 2 35 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 122 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 122 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 122 192 2 34 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 122 192 (accept_3_4 67 122 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 122 192 2 33 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 122 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 65
  122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 122 192 2 32 61 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 122 192
  (Polychromatic418967fa.accept_15_3_2_12_1_2469 63 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 122 192 2 31 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 122 192 (accept_3_4 61 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 122 192 2 30 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 122 192 (Polychromatic418967fa.accept_15_14_2_12_1_2472 59 122 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 122 192 2 29 61 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 122 192
  (Polychromatic418967fa.accept_17_6_3_5_1_3657 57 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 122 192 2 28 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 122 192 (accept_3_4 55 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 122 192 2 27 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 122 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 53 122 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 122 192 2 26 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 122 192
  (Polychromatic418967fa.accept_9_6_5_3_1_205 51 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 122 192 2 25 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 122 192 (accept_3_4 49 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 122 192 2 24 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 122 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 47 122 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 122 192 2 23 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 122 192
  (Polychromatic418967fa.accept_13_6_5_10_1_1213 45 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 122 192 2 22 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 122 192 (accept_3_4 43 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 122 192 2 21 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 122 192 (Polychromatic418967fa.accept_13_2_5_10_1_250 41 122 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 122 192 2 20 61 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 122 192
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 39 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 122 192 2 19 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 122 192 (accept_3_4 37 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 122 192 2 18 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 122 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 122 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 122 192 2 17 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 122 192
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 122 192 2 16 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 122 192 (accept_3_4 31 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 122 192 2 15 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 122 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 122 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 122 192 2 14 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 122 192
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 27 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 122 192 2 13 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 122 192 (accept_3_4 25 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 122 192 2 12 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 122 192 (Polychromatic418967fa.accept_17_6_3_5_1_3657 23 122 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 122 192 2 11 61 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 122 192
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 21 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 122 192 2 10 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 122 192 (accept_3_4 19 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 122 192 2 9 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 122 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 122 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 122 192 2 8 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 122 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 15
  122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 122 192 2 7 61 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 122 192 (accept_3_4 13
  122 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 122 192 2 6 61 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 122 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 122 192 2 5 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 122 192 (Polychromatic418967fa.accept_20_9_2_12_1_5144 9 122 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 122 192 2 4 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 122 192 (accept_3_4 7 122 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 122 192 2 3 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 122 192 (Polychromatic418967fa.accept_15_5_2_12_1_2543 5 122 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 122 192 2 2 61 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 122 192 (Polychromatic418967fa.accept_15_3_2_12_1_2469
  3 122 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 122 192 2 1 61 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 122 192 (accept_3_4 1
  122 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 72 121 192 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 121 192 (accept_3_5 71 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 121 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 121 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 121 192 (accept_3_5 68 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 121 192 (Polychromatic418967fa.accept_17_16_2_5_1_6031 67 121 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 121 192
  (Polychromatic418967fa.accept_10_6_1_2_1_874 66 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 121 192 (accept_3_5 65 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 121 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 64 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 121 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 121 192 (accept_3_5 62 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 121 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 121 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 121 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 60 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 121 192 (accept_3_5 59 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 121 192 (Polychromatic418967fa.accept_13_6_4_10_1_660 58 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 121 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 121 192 (accept_3_5 56 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 121 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 121 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 54 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 121 192 (accept_3_5 53 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 121 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 121 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 121 192 (accept_3_5 50 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 121 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 49 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 121 192
  (Polychromatic418967fa.accept_7_6_2_3_1_107 48 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 121 192 (accept_3_5 47 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 121 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 121 192 (Polychromatic418967fa.accept_13_6_4_10_1_660 45 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 121 192 (accept_3_5 44 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 121 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 121 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 121 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 121 192 (accept_3_5 41 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 121 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 40 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 121 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 121 192 (accept_3_5 38 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 121 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 121 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 121 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 36 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 121 192 (accept_3_5 35 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 121 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 34 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 121 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 121 192 (accept_3_5 32 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 121 192 (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 121 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 121 192
  (Polychromatic418967fa.accept_21_9_16_3_1_11133 30 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 121 192 (accept_3_5 29 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 121 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 121 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 121 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 121 192 (accept_3_5 26 121 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 121 192 (Polychromatic418967fa.accept_9_7_4_3_1_204
  25 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 121 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 121 192 (accept_3_5 23 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 121 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 22 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 121 192 (Polychromatic418967fa.accept_13_8_4_10_1_4358 21 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 121 192 (accept_3_5 20 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 121 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 121 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 121 192
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 18 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 121 192 (accept_3_5 17 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 121 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 121 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 121 192 (accept_3_5 14 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 121 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 121 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 12 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 121 192 (accept_3_5 11 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 121 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 121 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 121 192 (accept_3_5 8 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 121 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 121 192
  (Polychromatic418967fa.accept_7_6_2_3_1_107 6 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 121 192 (accept_3_5 5 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  121 192 (Polychromatic418967fa.accept_15_4_1_12_1_914 4 121 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 121 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 121 192 (accept_3_5 2 121 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 121 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 121 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 121
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 120 192 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 120 192 24 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 120 192 (Polychromatic418967fa.accept_13_6_3_10_1_698 71 120 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 120 192 2 35 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 120 192 3 23 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 120 192 4 17 30 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 120 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 120 192 6 11 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 120 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 65 120 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 120 192 8 8 15 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 120 192 3 21 40 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 120 192 2 31 60 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 120 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 192 12 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 192 (Polychromatic418967fa.accept_11_4_10_5_1_1202 59 120 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 120 192 2 29 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 120 192 3 19 40 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 120 192 8 7 15 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 120 192
  (Polychromatic418967fa.accept_17_4_1_5_1_2554 55 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 120 192 6 9 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 120 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 53 120 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 120 192 4 13 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 120 192 3 17 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 120 192 2 25 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 120 192
  (Polychromatic418967fa.accept_21_7_15_3_1_8029 49 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 192 24 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 120 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 47 120 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 120 192 2 23 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 120 192 3 15 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 120 192 4 11 30 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 120 192
  (Polychromatic418967fa.accept_21_1_15_3_1_4817 43 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 192 6 7 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 120 192 (Polychromatic418967fa.accept_13_2_3_10_1_658 41 120 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 120 192 8 5 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 120 192 3 13 40 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 120 192 2 19 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 120 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 192 12 3 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 192 (Polychromatic418967fa.accept_21_14_15_3_1_9580 35 120 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 120 192 2 17 60 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 120 192 3 11 40 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 120 192 8 4 15 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 120 192
  (Polychromatic418967fa.accept_19_12_6_2_1_5424 31 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 192 6 5 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 120 192 (Polychromatic418967fa.accept_19_10_6_2_1_6907 29 120 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 120 192 4 7 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 120 192 3 9 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 120 192 2 13 60 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 120 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 120 192 24 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 120 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 23 120 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 120 192 2 11 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 120 192 3 7 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 120 192 4 5 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 120 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 19
  120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 192 6 3 20 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 192
  (Polychromatic418967fa.accept_11_6_10_5_1_341 17 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 120 192 8 2 15 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 120 192 3 5 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 120 192 2 7 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 120 192 (Polychromatic418967fa.accept_19_13_6_2_1_4124 13 120 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 192 12 1 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 11
  120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 120 192 2 5 60 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 120 192 3 3 40 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 120 192 8 1 15 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 120 192
  (Polychromatic418967fa.accept_13_7_3_10_1_656 7 120 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 192 6 1 20 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 5 120 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 120 192 4 1 30 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 120 192 3 1 40 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 120 192 2 1 60 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 120 192 (Polychromatic418967fa.accept_19_1_6_2_1_8341 1 120 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 120
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 119 192 (Eq.refl
  Bool.true) (allA_succ_of_accept 73 119 192 (accept_3_4 73 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 119 192 (Polychromatic418967fa.accept_21_9_14_3_1_9678 72 119 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 119 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 71 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 119 192 (accept_3_4 70 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 119 192 (Polychromatic418967fa.accept_9_6_2_3_1_771
  69 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 119 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 68 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 119 192 (accept_3_4 67 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 119 192 (Polychromatic418967fa.accept_25_16_19_17_1_9285 66 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 65 119 192 (Polychromatic418967fa.accept_19_8_5_2_1_4105 65 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 119 192 (accept_3_4 64 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 192 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 119
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 192 (accept_3_4 61 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 192 (accept_3_4 58 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 192 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 192
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 56 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 119 192 (accept_3_4 55 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 119 192 (Polychromatic418967fa.accept_15_9_14_12_1_913 54 119 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 119 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 192 (accept_3_4 52 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 192 (Polychromatic418967fa.accept_9_6_2_3_1_771
  51 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 192 (accept_3_4 49 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 192 (Polychromatic418967fa.accept_19_10_5_2_1_9784 48 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 192 (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 192 (accept_3_4 46 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 192 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 119
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 192 (accept_3_4 43 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 192 (accept_3_4 40 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 192 (Polychromatic418967fa.accept_14_11_7_10_1_4852 39 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 192
  (Polychromatic418967fa.accept_13_12_2_10_1_2698 38 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 119 192 (accept_3_4 37 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 119 192 (Polychromatic418967fa.accept_19_17_5_2_1_2843 36 119 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 119 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 192 (accept_3_4 34 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 192 (Polychromatic418967fa.accept_9_6_2_3_1_771
  33 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 192 (accept_3_4 31 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 192 (Polychromatic418967fa.accept_21_9_14_3_1_9678 30 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 192 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 192 (accept_3_4 28 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 192 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 119
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 192 (accept_3_4 25 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 192 (accept_3_4 22 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 192
  (Polychromatic418967fa.accept_25_20_19_17_1_11157 20 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 119 192 (accept_3_4 19 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 119 192 (Polychromatic418967fa.accept_11_7_9_5_1_338 18 119 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 192 (accept_3_4 16 119 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 192 (Polychromatic418967fa.accept_9_6_2_3_1_771
  15 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 192 (accept_3_4 13 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 192 (Polychromatic418967fa.accept_13_12_2_10_1_2698 12 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 11 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 192 (accept_3_4 10 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 192 (Polychromatic418967fa.accept_15_9_14_12_1_913 9 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 192 (accept_3_4 7 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 192 (accept_3_4 4 119 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 192 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 119 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 192
  (Polychromatic418967fa.accept_15_2_14_12_1_2453 2 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 192 (accept_3_4 1 119 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 118 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 74 118 192 2 37 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 118 192 (Polychromatic418967fa.accept_14_3_6_10_1_752 73 118 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 118 192 2 36 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 118 192 (accept_3_5 71 118 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 118 192 2 35 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 118 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 69 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 118 192 2 34 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 118 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 118 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 118 192 2 33 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 118 192 (accept_3_5 65 118 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 118 192 2 32 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 118 192 (Polychromatic418967fa.accept_13_11_1_10_1_648
  63 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 118 192 2 31 59 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 118 192
  (Polychromatic418967fa.accept_9_7_1_3_1_443 61 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 118 192 2 30 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 118 192 (accept_3_5 59 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 118 192 2 29 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 118 192 (Polychromatic418967fa.accept_11_2_8_5_1_1219 57 118 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 118 192 2 28 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 118 192
  (Polychromatic418967fa.accept_10_5_8_2_1_517 55 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 118 192 2 27 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 118 192 (accept_3_5 53 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 118 192 2 26 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 118 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 51 118 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 118 192 2 25 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 118 192
  (Polychromatic418967fa.accept_9_4_1_3_1_190 49 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 118 192 2 24 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 118 192 (accept_3_5 47 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 118 192 2 23 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 118 192 (Polychromatic418967fa.accept_10_5_8_2_1_517 45 118 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 118 192 2 22 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 118 192
  (Polychromatic418967fa.accept_9_7_1_3_1_443 43 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 118 192 2 21 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 118 192 (accept_3_5 41 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 118 192 2 20 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 118 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 118 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 118 192 2 19 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 118 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 37 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 118 192 2 18 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 118 192 (accept_3_5 35 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 118 192 2 17 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 118 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 118 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 118 192 2 16 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 118 192
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 118 192 2 15 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 118 192 (accept_3_5 29 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 118 192 2 14 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 118 192 (Polychromatic418967fa.accept_18_9_10_12_1_5793 27 118 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 118 192 2 13 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 118 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 25 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 118 192 2 12 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 118 192 (accept_3_5 23 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 118 192 2 11 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 118 192 (Polychromatic418967fa.accept_17_4_16_5_1_8635 21 118 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 118 192 2 10 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 118 192
  (Polychromatic418967fa.accept_17_2_16_5_1_1584 19 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 118 192 2 9 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 118 192 (accept_3_5 17 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  118 192 2 8 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 118 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 118 192 2 7 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 118 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 118 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 118 192 2 6 59 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 118 192 (accept_3_5 11 118 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 118 192 2 5 59 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 118 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 9 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 118 192 2 4 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 118 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 118 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 118 192 2 3 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 118 192 (accept_3_5 5 118 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 118 192 2 2 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 118 192 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 118 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 118 192 2 1 59 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 118 192 (Polychromatic418967fa.accept_15_1_13_12_1_347
  1 118 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 117 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 117 192 3 25 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 117 192 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 117 192
  (Polychromatic418967fa.accept_19_16_3_2_1_6964 73 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 117 192 3 24 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 117 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 71 117 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 117 192
  (Polychromatic418967fa.accept_18_16_9_12_1_1182 70 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 69 117 192 3 23 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 68 117 192 (Polychromatic418967fa.accept_14_12_5_10_1_2130 68 117 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 117 192
  (Polychromatic418967fa.accept_20_7_17_12_1_11156 67 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 117 192 3 22 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 117 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 65 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 64 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 63 117 192 3 21 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 62 117 192 (Polychromatic418967fa.accept_17_11_15_5_1_3547 62 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 117 192
  (Polychromatic418967fa.accept_17_10_15_5_1_3606 61 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 117 192 3 20 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 117 192 (Polychromatic418967fa.accept_10_9_7_2_1_887 59 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 58 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 117 192 3 19 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 117 192 (Polychromatic418967fa.accept_19_18_3_2_1_6939 56 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 192
  (Polychromatic418967fa.accept_10_5_7_2_1_516 55 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 117 192 3 18 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 117 192 (Polychromatic418967fa.accept_11_9_7_5_1_749 53 117 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 117 192
  (Polychromatic418967fa.accept_18_16_9_12_1_1182 52 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 51 117 192 3 17 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 117 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 50 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 192
  (Polychromatic418967fa.accept_10_9_7_2_1_887 49 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 117 192 3 16 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 117 192 (Polychromatic418967fa.accept_17_13_15_5_1_3650 47 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 192
  (Polychromatic418967fa.accept_18_10_9_12_1_3259 46 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 117 192 3 15 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 117 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 44 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 117 192 3 14 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 117 192 (Polychromatic418967fa.accept_17_7_15_5_1_3649 41 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 117 192
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 117 192 3 13 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 117 192 (Polychromatic418967fa.accept_21_17_12_3_1_4848 38 117 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 117 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 37 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 117 192 3 12 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 117 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 117 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 192 (Polychromatic418967fa.accept_10_4_7_2_1_211
  34 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 117 192 3 11 39 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 117 192
  (Polychromatic418967fa.accept_21_11_12_3_1_6461 32 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 117 192 (Polychromatic418967fa.accept_11_9_7_5_1_749 31 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 192 3 10 39 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 29 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 192 (Polychromatic418967fa.accept_17_11_15_5_1_3547 28 117 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 192 3 9 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 192
  (Polychromatic418967fa.accept_14_12_5_10_1_2130 26 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 117 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 25 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 192 3 8 39 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 23 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 117 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 117 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 117 192 3 7 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 117 192 (Polychromatic418967fa.accept_11_9_7_5_1_749
  20 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 192
  (Polychromatic418967fa.accept_10_9_7_2_1_887 19 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 117 192 3 6 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 117 192 (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 117 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 117 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 16
  117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 192 3 5 39 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 192
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 117 192 (Polychromatic418967fa.accept_17_13_15_5_1_3650 13 117 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 117 192 3 4 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 117 192
  (Polychromatic418967fa.accept_17_11_15_5_1_3547 11 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 117 192 (Polychromatic418967fa.accept_17_10_15_5_1_3606 10 117 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 192 3 3 39 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 8 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 192 (Polychromatic418967fa.accept_17_7_15_5_1_3649 7 117 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 192 3 2 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 117 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 192
  (Polychromatic418967fa.accept_10_4_7_2_1_211 4 117 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 192 3 1 39 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 2 117 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 117 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 116 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 76 116 192 4 19 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 75 116 192 (Polychromatic418967fa.accept_18_3_8_12_1_3283 75 116 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 116 192 2 37 58 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 116 192 (accept_3_4 73 116 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 116 192 4 18 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 116 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 71 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 116 192 2 35 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 116 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 116 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 116 192 4 17 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 116 192 (accept_3_4 67 116 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 116 192 2 33 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 116 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 65
  116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 116 192 4 16 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 116 192
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 63 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 116 192 2 31 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 116 192 (accept_3_4 61 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 116 192 4 15 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 116 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 116 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 116 192 2 29 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 116 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 57 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 116 192 4 14 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 116 192 (accept_3_4 55 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 116 192 2 27 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 116 192 (Polychromatic418967fa.accept_15_8_11_12_1_1626 53 116 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 116 192 4 13 29 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 116 192
  (Polychromatic418967fa.accept_9_6_8_3_1_183 51 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 116 192 2 25 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 116 192 (accept_3_4 49 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 116 192 4 12 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 116 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 47 116 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 116 192 2 23 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 116 192
  (Polychromatic418967fa.accept_11_1_6_5_1_1732 45 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 116 192 4 11 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 116 192 (accept_3_4 43 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 116 192 2 21 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 116 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 116 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 116 192 4 10 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 116 192
  (Polychromatic418967fa.accept_18_3_8_12_1_3283 39 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 116 192 2 19 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 116 192 (accept_3_4 37 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 116 192 4 9 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 116 192 (Polychromatic418967fa.accept_13_9_12_10_1_242 35 116 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 116 192 2 17 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 116 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 33
  116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 116 192 4 8 29 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 116 192 (accept_3_4 31
  116 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 116 192 2 15 58 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 116 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 29 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 116 192 4 7 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 116 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 116 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 116 192 2 13 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 116 192 (accept_3_4 25 116 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 116 192 4 6 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 116 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 116 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 116 192 2 11 58 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 116 192
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 116 192 4 5 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 116 192 (accept_3_4 19 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  116 192 2 9 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  17 116 192 (Polychromatic418967fa.accept_28_17_4_24_1_11155 17 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 16 116 192 4 4 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 116 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 116 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 116 192 2 7 58 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 116 192 (accept_3_4 13
  116 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 116 192 4 3 29 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 116 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 116 192 2 5 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 116 192 (Polychromatic418967fa.accept_13_9_12_10_1_242 9 116 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 116 192 4 2 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 116 192 (accept_3_4 7 116 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 116 192 2 3 58 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 116 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 116 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 116 192 4 1 29 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 116 192 (Polychromatic418967fa.accept_18_3_8_12_1_3283
  3 116 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 116 192 2 1 58 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 116 192 (accept_3_4 1
  116 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 78 115 192 (Eq.refl
  Bool.true) (allA_succ_of_accept 77 115 192 (accept_3_5 77 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 115 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 115 192 (Polychromatic418967fa.accept_18_3_7_12_1_1196 75 115
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 115 192 (accept_3_5 74 115
  192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 115 192
  (Polychromatic418967fa.accept_9_1_7_3_1_41 73 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 115 192 (Polychromatic418967fa.accept_19_15_1_2_1_6894 72 115 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 115 192 (accept_3_5 71 115 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 115 192 (Polychromatic418967fa.accept_19_13_1_2_1_11154 70 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 115 192
  (Polychromatic418967fa.accept_9_6_7_3_1_436 69 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 115 192 (accept_3_5 68 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 67 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 192 (Polychromatic418967fa.accept_13_1_11_10_1_1258 66 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 192 (accept_3_5 65 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 115 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 192
  (Polychromatic418967fa.accept_10_3_5_2_1_38 63 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 192 (accept_3_5 62 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 192 (Polychromatic418967fa.accept_17_10_13_5_1_3513 61 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 60 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 192 (accept_3_5 59 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 192
  (Polychromatic418967fa.accept_10_7_5_2_1_880 57 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 192 (accept_3_5 56 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 192 (Polychromatic418967fa.accept_13_2_11_10_1_1881 54 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 192 (accept_3_5 53 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 192 (Polychromatic418967fa.accept_15_7_10_12_1_2403 52 115
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 192
  (Polychromatic418967fa.accept_9_6_7_3_1_436 51 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 192 (accept_3_5 50 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 192 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 192 (accept_3_5 47 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 115 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 192
  (Polychromatic418967fa.accept_19_7_1_2_1_9792 45 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 192 (accept_3_5 44 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 192 (Polychromatic418967fa.accept_10_3_5_2_1_38 43 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 192 (accept_3_5 41 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 192
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 39 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 115 192 (accept_3_5 38 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 115 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 115 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 115 192 (Polychromatic418967fa.accept_15_6_10_12_1_2538 36 115
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 192 (accept_3_5 35 115
  192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 192
  (Polychromatic418967fa.accept_13_8_11_10_1_636 34 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 115 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 33 115 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 115 192 (accept_3_5 32 115 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 115 192
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 30 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 115 192 (accept_3_5 29 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 115 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 115 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 115
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 115 192 (accept_3_5 26 115
  192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 115 192
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 192 (accept_3_5 23 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 192
  (Polychromatic418967fa.accept_13_8_11_10_1_636 21 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 192 (accept_3_5 20 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 192 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 192 (accept_3_5 17 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 192 (Polychromatic418967fa.accept_13_3_11_10_1_2647 16 115
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 192
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 192 (accept_3_5 14 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 192 (Polychromatic418967fa.accept_13_12_11_10_1_2711 12 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 192 (accept_3_5 11 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 115 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 192
  (Polychromatic418967fa.accept_15_9_10_12_1_1625 9 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 192 (accept_3_5 8 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 192 (Polychromatic418967fa.accept_10_7_5_2_1_880 7 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 192 (accept_3_5 5 115 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 115 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 192
  (Polychromatic418967fa.accept_10_3_5_2_1_38 3 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 192 (accept_3_5 2 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 115 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 79 114 192 (Eq.refl Bool.true) (allA_succ_of_gcd 78 114 192 6 13 19 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 114 192
  (Polychromatic418967fa.accept_9_5_6_3_1_40 77 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 114 192 2 38 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 114 192 3 25 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 74 114 192 2 37 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 114 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 73 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 114 192 6 12 19 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 114 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 71 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 114 192 2 35 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 69 114 192 3 23 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 68 114 192 2 34 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 114 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 67 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 114 192 6 11 19 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 114 192
  (Polychromatic418967fa.accept_9_2_6_3_1_178 65 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 114 192 2 32 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 63 114 192 3 21 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 62 114 192 2 31 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 114 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 61 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 114 192 6 10 19 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 114 192
  (Polychromatic418967fa.accept_9_5_6_3_1_40 59 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 114 192 2 29 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 57 114 192 3 19 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 56 114 192 2 28 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 114 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 55 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 114 192 6 9 19 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 114 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 114 192 2 26 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 114 192 3 17 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 50 114 192 2 25 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 114 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 49 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 114 192 6 8 19 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 114 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 47 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 114 192 2 23 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 45 114 192 3 15 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 114 192 2 22 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 114 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 43 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 114 192 6 7 19 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 192
  (Polychromatic418967fa.accept_7_6_2_3_1_107 41 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 114 192 2 20 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 39 114 192 3 13 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 38 114 192 2 19 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 114 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 37 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 192 6 6 19 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 114 192 2 17 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 114 192 3 11 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 114 192 2 16 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 114 192 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 114 192 6 5 19 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 114 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 29 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 114 192 2 14 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 114 192 3 9 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 114 192 2 13 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 114 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 114 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 192 6 4 19 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 192
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 114 192 2 11 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 114 192 3 7 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 114 192 2 10 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 114 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 19 114 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 192 6 3 19 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 114 192 2 8 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 114 192 3 5 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 114 192 2 7 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 114 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 13 114 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 114 192 6 2 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 114 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 114 192 2 5 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 114 192 3 3 38 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 114 192 2 4 57 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 114 192
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 114 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 114 192 6 1 19 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 114 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 114 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 114 192 2 2 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 114 192 3 1 38 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 114 192 2 1 57 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 114 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 1 114 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 113 192 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 113 192 (accept_3_4 79 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 113 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 113 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 113 192 (Polychromatic418967fa.accept_13_12_9_10_1_1223 77 113
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 113 192 (accept_3_4 76 113
  192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 113 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 75 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 74 113 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 74 113 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 113 192 (accept_3_4 73 113 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 72 113 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 72 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 113 192 (Polychromatic418967fa.accept_9_8_5_3_1_777
  71 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 113 192 (accept_3_4 70
  113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 113 192
  (Polychromatic418967fa.accept_9_6_5_3_1_205 69 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 113 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 68 113 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 192 (accept_3_4 67 113 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 113 192 (Polychromatic418967fa.accept_13_1_9_10_1_625 66 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 65 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 192 (accept_3_4 64 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 192 (Polychromatic418967fa.accept_11_8_3_5_1_355 63 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 62 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 192 (accept_3_4 61 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 60 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 192
  (Polychromatic418967fa.accept_20_19_13_12_1_2476 59 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 113 192 (accept_3_4 58 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 113 192 (Polychromatic418967fa.accept_17_6_11_5_1_3506 57 113 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 113 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 56 113 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 192 (accept_3_4 55 113 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 192 (Polychromatic418967fa.accept_7_5_1_3_1_103
  54 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 53 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 192 (accept_3_4 52 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 192 (Polychromatic418967fa.accept_15_5_8_12_1_2435 50 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 192 (accept_3_4 49 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 192 (Polychromatic418967fa.accept_15_3_8_12_1_900 48 113
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 47 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 192 (accept_3_4 46 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 192 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 44 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 192 (accept_3_4 43 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 192
  (Polychromatic418967fa.accept_10_1_3_2_1_220 41 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 192 (accept_3_4 40 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 192 (accept_3_4 37 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 192 (Polychromatic418967fa.accept_21_15_8_3_1_8086 36 113 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 192 (accept_3_4 34 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 32 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 192 (accept_3_4 31 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 30 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 192 (accept_3_4 28 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 192 (Polychromatic418967fa.accept_13_1_9_10_1_625 27 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 26 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 192 (accept_3_4 25 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 23 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 192 (accept_3_4 22 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 192 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 192 (accept_3_4 19 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 18 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 192 (accept_3_4 16 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 192 (Polychromatic418967fa.accept_13_1_9_10_1_625 14 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 192 (accept_3_4 13 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 12 113 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 11 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 192 (accept_3_4 10 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 9 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 192 (accept_3_4 7 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 113 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 5 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 192 (accept_3_4 4 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 192 (Polychromatic418967fa.accept_15_3_8_12_1_900 3 113 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 2 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 192 (accept_3_4 1 113 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 112 192 (Eq.refl Bool.true) (allA_succ_of_gcd 80 112 192 16 5 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 112 192
  (Polychromatic418967fa.accept_9_7_4_3_1_204 79 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 112 192 2 39 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 112 192 (accept_3_5 77 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 112 192 4 19 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 112 192 (Polychromatic418967fa.accept_21_12_7_3_1_4927 75 112 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 112 192 2 37 56 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 112 192
  (Polychromatic418967fa.accept_9_1_4_3_1_201 73 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 112 192 8 9 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 112 192 (accept_3_5 71 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70
  112 192 2 35 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 69 112 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 112 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 112 192 4 17 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 112 192 (Polychromatic418967fa.accept_13_2_8_10_1_1902
  67 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 112 192 2 33 56 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 112 192
  (accept_3_5 65 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 112 192 16 4 7 12 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 112 192
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 63 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 112 192 2 31 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 112 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 112 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 112 192 4 15 28 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 112 192 (accept_3_5 59 112 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 112 192 2 29 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 112 192 (Polychromatic418967fa.accept_13_5_8_10_1_4363
  57 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 112 192 8 7 14 24
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 112 192
  (Polychromatic418967fa.accept_9_1_4_3_1_201 55 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 112 192 2 27 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 112 192 (accept_3_5 53 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 112 192 4 13 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 112 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 112 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 112 192 2 25 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 112 192
  (Polychromatic418967fa.accept_15_4_7_12_1_5538 49 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 112 192 16 3 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 112 192 (accept_3_5 47 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46
  112 192 2 23 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 45 112 192 (Polychromatic418967fa.accept_18_9_4_12_1_3209 45 112 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 112 192 4 11 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 112 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 43
  112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 112 192 2 21 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 112 192 (accept_3_5 41
  112 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 112 192 8 5 14 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 112 192
  (Polychromatic418967fa.accept_25_14_12_17_1_11153 39 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 38 112 192 2 19 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 112 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 112 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 112 192 4 9 28 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 112 192 (accept_3_5 35 112 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 112 192 2 17 56 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 112 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 112 192 16 2 7 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 112 192 (Polychromatic418967fa.accept_13_5_8_10_1_4363 31 112 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 112 192 2 15 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 112 192 (accept_3_5 29 112 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 28 112 192 4 7 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 112 192 (Polychromatic418967fa.accept_18_9_4_12_1_3209 27 112
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 112 192 2 13 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 112 192
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 112 192 8 3 14 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 112 192 (accept_3_5 23 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  112 192 2 11 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 112 192 (Polychromatic418967fa.accept_15_6_7_12_1_869 21 112 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 112 192 4 5 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 112 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 19
  112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 112 192 2 9 56 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 112 192 (accept_3_5 17
  112 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 112 192 16 1 7 12 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 112 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 112 192 2 7 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 112 192 (Polychromatic418967fa.accept_17_13_10_5_1_2566 13 112 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 112 192 4 3 28 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 112 192 (accept_3_5 11 112 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 112 192 2 5 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 112 192 (Polychromatic418967fa.accept_18_9_4_12_1_3209
  9 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 112 192 8 1 14 24 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 112 192
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 112 192 2 3 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 112 192 (accept_3_5 5 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 112
  192 4 1 28 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  112 192 (Polychromatic418967fa.accept_15_3_7_12_1_372 3 112 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 112 192 2 1 56 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 112 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 112 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 111 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 111 192 3 27 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 111 192 (Polychromatic418967fa.accept_15_5_6_12_1_916 80 111 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 111 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 79 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 111 192 3 26 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 111 192 (Polychromatic418967fa.accept_13_12_7_10_1_2662 77 111 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 111 192
  (Polychromatic418967fa.accept_10_6_1_2_1_874 76 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 111 192 3 25 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 111 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 74 111 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 111 192 (Polychromatic418967fa.accept_10_3_1_2_1_521
  73 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 111 192 3 24 37 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 111 192
  (Polychromatic418967fa.accept_19_14_16_2_1_6952 71 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 70 111 192 (Polychromatic418967fa.accept_15_10_6_12_1_1645 70 111 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 111 192 3 23 37 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 111 192
  (Polychromatic418967fa.accept_13_3_7_10_1_668 68 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 111 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 67 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 111 192 3 22 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 111 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 65
  111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 192
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 64 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 111 192 3 21 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 111 192 (Polychromatic418967fa.accept_15_2_6_12_1_1613 62 111 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 192
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 61 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 111 192 3 20 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 111 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 59 111 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 192 (Polychromatic418967fa.accept_7_2_6_3_1_100
  58 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 111 192 3 19 37 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 111 192
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 111 192 (Polychromatic418967fa.accept_13_3_7_10_1_668 55 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 111 192 3 18 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 111 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 53
  111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 192
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 52 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 111 192 3 17 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 111 192 (Polychromatic418967fa.accept_11_6_1_5_1_2388 50 111 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 192
  (Polychromatic418967fa.accept_10_9_1_2_1_522 49 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 111 192 3 16 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 111 192 (Polychromatic418967fa.accept_13_8_7_10_1_4362 47 111 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 46 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 111 192 3 15 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 111 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 44 111 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 111 192 (Polychromatic418967fa.accept_10_3_1_2_1_521
  43 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 192 3 14 37 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 192
  (Polychromatic418967fa.accept_17_7_9_5_1_2588 41 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 192 (Polychromatic418967fa.accept_15_10_6_12_1_1645 40 111 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 192 3 13 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 192
  (Polychromatic418967fa.accept_13_12_7_10_1_2662 38 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 111 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 37 111 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 111 192 3 12 37 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 111 192
  (Polychromatic418967fa.accept_15_5_6_12_1_916 35 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 111 192 (Polychromatic418967fa.accept_13_8_7_10_1_4362 34 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 111 192 3 11 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 111 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 32
  111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 192
  (Polychromatic418967fa.accept_14_3_13_10_1_761 31 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 111 192 3 10 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 111 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 111 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 111 192 (Polychromatic418967fa.accept_11_6_1_5_1_2388
  28 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 192 3 9 37 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 192
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 111 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 25 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 111 192 3 8 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 111 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 23
  111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 192
  (Polychromatic418967fa.accept_15_7_6_12_1_1614 22 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 111 192 3 7 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 111 192 (Polychromatic418967fa.accept_15_5_6_12_1_916 20 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 111 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 19 111
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 192 3 6 37 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 192
  (Polychromatic418967fa.accept_11_6_1_5_1_2388 17 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 111 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 16 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 111 192 3 5 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 111 192 (Polychromatic418967fa.accept_17_14_9_5_1_4755
  14 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 192
  (Polychromatic418967fa.accept_10_3_1_2_1_521 13 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 111 192 3 4 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 111 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 11 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 192 (Polychromatic418967fa.accept_15_10_6_12_1_1645 10 111
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 111 192 3 3 37 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 111 192
  (Polychromatic418967fa.accept_13_8_7_10_1_4362 8 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 111 192 (Polychromatic418967fa.accept_15_7_6_12_1_1614 7 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 192 3 2 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 192 (Polychromatic418967fa.accept_15_5_6_12_1_916 5 111 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 111 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 4 111 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 111 192 3 1 37 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 111 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 2 111 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 192 (Polychromatic418967fa.accept_18_1_3_12_1_467 1 111 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 111
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 110 192 (Eq.refl
  Bool.true) (allA_succ_of_gcd 82 110 192 2 41 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 81 110 192 (Polychromatic418967fa.accept_13_3_6_10_1_2658 81 110 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 110 192 2 40 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 110 192 (accept_3_4 79 110 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 110 192 2 39 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 110 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 76 110 192 2 38 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 75 110 192 (Polychromatic418967fa.accept_14_5_12_10_1_2985 75 110 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 110 192 2 37 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 110 192 (accept_3_4 73 110 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 110 192 2 36 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 110 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 71 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 110 192 2 35 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 110 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 110 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 110 192 2 34 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 110 192 (accept_3_4 67 110 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 110 192 2 33 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 110 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 65
  110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 110 192 2 32 55 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 110 192
  (Polychromatic418967fa.accept_17_12_8_5_1_6018 63 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 110 192 2 31 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 110 192 (accept_3_4 61 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 110 192 2 30 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 110 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 110 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 110 192 2 29 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 110 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 57 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 110 192 2 28 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 110 192 (accept_3_4 55 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 110 192 2 27 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 110 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 110 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 110 192 2 26 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 110 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 51 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 110 192 2 25 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 110 192 (accept_3_4 49 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 110 192 2 24 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 110 192 (Polychromatic418967fa.accept_14_5_12_10_1_2985 47 110 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 110 192 2 23 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 110 192
  (Polychromatic418967fa.accept_20_5_10_12_1_8200 45 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 110 192 2 22 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 110 192 (accept_3_4 43 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 110 192 2 21 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 110 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 110 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 110 192 2 20 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 110 192
  (Polychromatic418967fa.accept_15_9_5_12_1_1640 39 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 110 192 2 19 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 110 192 (accept_3_4 37 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 110 192 2 18 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 110 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 110 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 110 192 2 17 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 110 192
  (Polychromatic418967fa.accept_9_6_2_3_1_771 33 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 110 192 2 16 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 110 192 (accept_3_4 31 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 110 192 2 15 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 110 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 29 110 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 110 192 2 14 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 110 192
  (Polychromatic418967fa.accept_19_8_15_2_1_6961 27 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 110 192 2 13 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 110 192 (accept_3_4 25 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 110 192 2 12 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 110 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 23 110 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 110 192 2 11 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 110 192
  (Polychromatic418967fa.accept_15_6_5_12_1_1642 21 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 110 192 2 10 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 110 192 (accept_3_4 19 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 110 192 2 9 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 110 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 110 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 110 192 2 8 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 110 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 15
  110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 110 192 2 7 55 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 110 192 (accept_3_4 13
  110 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 110 192 2 6 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 110 192
  (Polychromatic418967fa.accept_19_11_15_2_1_4096 11 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 110 192 2 5 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 110 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 9 110 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 110 192 2 4 55 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 110 192 (accept_3_4 7 110 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 110 192 2 3 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 110 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 110 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 110 192 2 2 55 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 110 192
  (Polychromatic418967fa.accept_13_3_6_10_1_2658 3 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 110 192 2 1 55 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 110 192 (accept_3_4 1 110 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 84 109 192 (Eq.refl
  Bool.true) (allA_succ_of_accept 83 109 192 (accept_3_5 83 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 109 192 (Polychromatic418967fa.accept_13_4_5_10_1_1247 82 109 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 109 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 81 109 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 109 192 (accept_3_5 80 109 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 109 192 (Polychromatic418967fa.accept_9_7_1_3_1_443
  79 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 109 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 78 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 109 192 (accept_3_5 77 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 109 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 76 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 109 192 (Polychromatic418967fa.accept_18_3_1_12_1_4419 75 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 109 192 (accept_3_5 74 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 109 192 (Polychromatic418967fa.accept_13_8_5_10_1_2701 73 109
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 192
  (Polychromatic418967fa.accept_11_6_10_5_1_341 72 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 109 192 (accept_3_5 71 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 109 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 70 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 109 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 69 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 192 (accept_3_5 68 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 109 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 192
  (Polychromatic418967fa.accept_17_15_7_5_1_9836 66 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 109 192 (accept_3_5 65 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 109 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 64 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 109 192 (Polychromatic418967fa.accept_14_7_11_10_1_2155 63 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 192 (accept_3_5 62 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 109 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 61 109 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 60 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 109 192 (accept_3_5 59 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 109 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 58 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 109 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 57 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 192 (accept_3_5 56 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 109 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 55 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 192
  (Polychromatic418967fa.accept_13_2_5_10_1_250 54 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 192 (accept_3_5 53 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 192 (accept_3_5 50 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 48 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 192 (accept_3_5 47 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 192 (Polychromatic418967fa.accept_15_1_4_12_1_2401 46 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 192 (Polychromatic418967fa.accept_13_6_5_10_1_1213 45 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 192 (accept_3_5 44 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 43 109 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 192 (accept_3_5 41 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 40 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 192 (Polychromatic418967fa.accept_11_6_10_5_1_341 39 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 192 (accept_3_5 38 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 192 (Polychromatic418967fa.accept_10_7_9_2_1_1887 37 109
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 36 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 192 (accept_3_5 35 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 34 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 192 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 192 (accept_3_5 32 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 192
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 30 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 192 (accept_3_5 29 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 192 (Polychromatic418967fa.accept_11_6_10_5_1_341 28 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 27 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 192 (accept_3_5 26 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 192
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 192 (accept_3_5 23 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 22 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 192 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 192 (accept_3_5 20 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 192 (Polychromatic418967fa.accept_13_6_5_10_1_1213 19 109 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 192
  (Polychromatic418967fa.accept_21_18_4_3_1_8082 18 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 192 (accept_3_5 17 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 15 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 192 (accept_3_5 14 109 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 13 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 192
  (Polychromatic418967fa.accept_17_12_7_5_1_8659 12 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 192 (accept_3_5 11 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 192 (Polychromatic418967fa.accept_27_10_1_3_1_11152 10 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 192 (Polychromatic418967fa.accept_15_9_4_12_1_1611 9 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 192 (accept_3_5 8 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 192 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 109 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 6 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 192 (accept_3_5 5 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 192 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 109 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 192 (Polychromatic418967fa.accept_18_3_1_12_1_4419 3 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 192 (accept_3_5 2 109 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 109 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 108 192
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 108 192 12 7 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 83 108 192 (Polychromatic418967fa.accept_13_5_4_10_1_1244 83 108 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 108 192 2 41 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 108 192 3 27 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 108 192 4 20 27 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 108 192
  (Polychromatic418967fa.accept_13_1_4_10_1_622 79 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 108 192 6 13 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 108 192 (Polychromatic418967fa.accept_15_2_3_12_1_891 77 108 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 108 192 4 19 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 108 192 3 25 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 108 192 2 37 54 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 108 192
  (Polychromatic418967fa.accept_11_7_9_5_1_338 73 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 108 192 12 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 108 192 (Polychromatic418967fa.accept_13_6_4_10_1_660 71 108 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 108 192 2 35 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 108 192 3 23 36 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 108 192 4 17 27 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 108 192
  (Polychromatic418967fa.accept_15_7_3_12_1_365 67 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 108 192 6 11 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 108 192 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 108 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 108 192 4 16 27 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 108 192 3 21 36 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 108 192 2 31 54 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 108 192
  (Polychromatic418967fa.accept_23_15_16_8_1_11151 61 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 60 108 192 12 5 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 59 108 192 (Polychromatic418967fa.accept_13_7_4_10_1_2675 59 108 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 108 192 2 29 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 108 192 3 19 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 108 192 4 14 27 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 108 192
  (Polychromatic418967fa.accept_10_5_8_2_1_517 55 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 108 192 6 9 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 108 192 (Polychromatic418967fa.accept_13_1_4_10_1_622 53 108 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 108 192 4 13 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 108 192 3 17 36 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 108 192 2 25 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 108 192
  (Polychromatic418967fa.accept_19_11_13_2_1_9770 49 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 48 108 192 12 4 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 108 192 (Polychromatic418967fa.accept_13_8_4_10_1_4358 47 108 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 108 192 2 23 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 108 192 3 15 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 108 192 4 11 27 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 108 192
  (Polychromatic418967fa.accept_15_13_3_12_1_1609 43 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 108 192 6 7 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 108 192 (Polychromatic418967fa.accept_23_18_16_8_1_11150 41 108 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 108 192 4 10 27 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 108 192 3 13 36 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 108 192 2 19 54
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 108 192
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 37 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 108 192 12 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 108 192 (Polychromatic418967fa.accept_10_5_8_2_1_517 35 108 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 108 192 2 17 54 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 108 192 3 11 36 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 108 192 4 8 27 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 108 192
  (Polychromatic418967fa.accept_13_5_4_10_1_1244 31 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 192 6 5 18 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 108 192 (Polychromatic418967fa.accept_11_7_9_5_1_338 29 108 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 108 192 4 7 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 108 192 3 9 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 108 192 2 13 54 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 108 192
  (Polychromatic418967fa.accept_10_5_8_2_1_517 25 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 192 12 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 192 (Polychromatic418967fa.accept_15_8_3_12_1_1657 23 108 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 108 192 2 11 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 108 192 3 7 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 108 192 4 5 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 108 192 (Polychromatic418967fa.accept_13_6_4_10_1_660
  19 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 192 6 3 18 32
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 192
  (Polychromatic418967fa.accept_15_2_3_12_1_891 17 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 108 192 4 4 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 108 192 3 5 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 108 192 2 7 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 108 192 (Polychromatic418967fa.accept_15_13_3_12_1_1609 13 108 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 192 12 1 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 192
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 108 192 2 5 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 108 192 3 3 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 108 192 4 2 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 108 192 (Polychromatic418967fa.accept_11_7_9_5_1_338 7 108 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 108 192 6 1 18 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 108 192
  (Polychromatic418967fa.accept_10_5_8_2_1_517 5 108 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 108 192 4 1 27 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 108 192 3 1 36 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 108 192 2 1 54 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 108 192 (Polychromatic418967fa.accept_13_1_4_10_1_622 1 108 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 107 192
  (Eq.refl Bool.true) (allA_succ_of_accept 85 107 192 (accept_3_4 85 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 84 107 192 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 107 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 107 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 83 107 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 107 192 (accept_3_4 82 107 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 107 192 (Polychromatic418967fa.accept_15_6_2_12_1_885
  81 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 107 192
  (Polychromatic418967fa.accept_11_3_8_5_1_336 80 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 107 192 (accept_3_4 79 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 107 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 78 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 107 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 77 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 107 192 (accept_3_4 76 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 107 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 75 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 74 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 107 192 (accept_3_4 73 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 107 192 (Polychromatic418967fa.accept_13_7_3_10_1_656 72 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 107 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 71 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 107 192 (accept_3_4 70 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 107 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 69 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 107 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 68 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 107 192 (accept_3_4 67 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 107 192 (Polychromatic418967fa.accept_15_6_2_12_1_885 66 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 107 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 65 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 107 192 (accept_3_4 64 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 107 192 (Polychromatic418967fa.accept_13_11_3_10_1_4374 63 107 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 107 192
  (Polychromatic418967fa.accept_7_6_2_3_1_107 62 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 107 192 (accept_3_4 61 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 107 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 107 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 59 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 107 192 (accept_3_4 58 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 107 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 57 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 107 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 107 192 (accept_3_4 55 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 107 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 54 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 107 192 (Polychromatic418967fa.accept_23_7_15_8_1_9478 53 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 107 192 (accept_3_4 52 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 107 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 107 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 107 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 50 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 107 192 (accept_3_4 49 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 107 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 48 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 107 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 47 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 107 192 (accept_3_4 46 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 107 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 107 192
  (Polychromatic418967fa.accept_10_4_7_2_1_211 44 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 107 192 (accept_3_4 43 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 107 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 107 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 41 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 107 192 (accept_3_4 40 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 107 192 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 107 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 38 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 107 192 (accept_3_4 37 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 107 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 36 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 107 192 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 107 192 (accept_3_4 34 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 107 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 33 107 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 107 192
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 107 192 (accept_3_4 31 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 107 192 (Polychromatic418967fa.accept_21_9_2_3_1_11138 30 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 107 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 29 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 107 192 (accept_3_4 28 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 107 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 27 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 107 192
  (Polychromatic418967fa.accept_7_5_2_3_1_106 26 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 107 192 (accept_3_4 25 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 107 192 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 107 192 (Polychromatic418967fa.accept_9_5_8_3_1_437 23 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 107 192 (accept_3_4 22 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 107 192 (Polychromatic418967fa.accept_15_6_2_12_1_885 21 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 107 192
  (Polychromatic418967fa.accept_7_6_2_3_1_107 20 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 107 192 (accept_3_4 19 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 107 192 (Polychromatic418967fa.accept_15_3_2_12_1_2469 18 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 107 192 (Polychromatic418967fa.accept_19_17_12_2_1_6880 17 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 107 192 (accept_3_4 16 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 107 192 (Polychromatic418967fa.accept_7_1_2_3_1_257 15 107 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 107 192
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 107 192 (accept_3_4 13 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 107 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 12 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 107 192 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 107 192 (accept_3_4 10 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 107 192 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 107 192
  (Polychromatic418967fa.accept_7_1_2_3_1_257 8 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 107 192 (accept_3_4 7 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  107 192 (Polychromatic418967fa.accept_7_6_2_3_1_107 6 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 107 192 (Polychromatic418967fa.accept_7_5_2_3_1_106 5 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 107 192 (accept_3_4 4 107 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 107 192 (Polychromatic418967fa.accept_11_3_8_5_1_336 3 107 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 107 192
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 107 192 (accept_3_4 1 107 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 107
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 87 106 192
  (Eq.refl Bool.true) (allA_succ_of_gcd 86 106 192 2 43 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 106 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 85 106 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 106 192 2 42 53 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 106 192 (accept_3_5 83
  106 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 106 192 2 41 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 106 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 81 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 106 192 2 40 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 106 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 79 106 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 106 192 2 39 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 106 192 (accept_3_5 77 106 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 106 192 2 38 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 106 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 75
  106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 106 192 2 37 53 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 106 192
  (Polychromatic418967fa.accept_9_1_7_3_1_41 73 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 106 192 2 36 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 106 192 (accept_3_5 71 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 106 192 2 35 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 106 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 69 106 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 106 192 2 34 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 106 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 67 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 106 192 2 33 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 106 192 (accept_3_5 65 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 106 192 2 32 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 106 192 (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 106 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 106 192 2 31 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 106 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 61 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 106 192 2 30 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 106 192 (accept_3_5 59 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 106 192 2 29 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 106 192 (Polychromatic418967fa.accept_13_5_2_10_1_248 57 106 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 106 192 2 28 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 106 192
  (Polychromatic418967fa.accept_9_1_7_3_1_41 55 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 106 192 2 27 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 106 192 (accept_3_5 53 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 106 192 2 26 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 106 192 (Polychromatic418967fa.accept_7_2_1_3_1_102 51 106 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 106 192 2 25 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 106 192
  (Polychromatic418967fa.accept_9_4_7_3_1_43 49 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 106 192 2 24 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 106 192 (accept_3_5 47 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 106 192 2 23 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 106 192 (Polychromatic418967fa.accept_13_6_2_10_1_1240 45 106 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 106 192 2 22 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 106 192
  (Polychromatic418967fa.accept_15_13_1_12_1_1638 43 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 106 192 2 21 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 106 192 (accept_3_5 41 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 106 192 2 20 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 106 192 (Polychromatic418967fa.accept_7_4_1_3_1_277 39 106 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 106 192 2 19 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 106 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 37 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 106 192 2 18 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 106 192 (accept_3_5 35 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 106 192 2 17 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 106 192 (Polychromatic418967fa.accept_7_5_1_3_1_103 33 106 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 106 192 2 16 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 106 192
  (Polychromatic418967fa.accept_9_4_7_3_1_43 31 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 106 192 2 15 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 106 192 (accept_3_5 29 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 106 192 2 14 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 106 192 (Polychromatic418967fa.accept_18_9_16_12_1_1143 27 106 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 106 192 2 13 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 106 192
  (Polychromatic418967fa.accept_7_4_1_3_1_277 25 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 106 192 2 12 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 106 192 (accept_3_5 23 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 106 192 2 11 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 106 192 (Polychromatic418967fa.accept_10_1_6_2_1_867 21 106 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 106 192 2 10 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 106 192
  (Polychromatic418967fa.accept_7_5_1_3_1_103 19 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 106 192 2 9 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 106 192 (accept_3_5 17 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16
  106 192 2 8 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  15 106 192 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 106 192 2 7 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 106 192 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 106 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 106 192 2 6 53 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 106 192 (accept_3_5 11 106 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 106 192 2 5 53 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 106 192
  (Polychromatic418967fa.accept_7_2_1_3_1_102 9 106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 106 192 2 4 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 106 192 (Polychromatic418967fa.accept_20_7_6_12_1_6650 7 106 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 106 192 2 3 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 106 192 (accept_3_5 5 106 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 106 192 2 2 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 106 192 (Polychromatic418967fa.accept_13_3_2_10_1_2697 3 106 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 106 192 2 1 53 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 106 192 (Polychromatic418967fa.accept_9_1_7_3_1_41 1
  106 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 105 192
  (Eq.refl Bool.true) (allA_succ_of_gcd 87 105 192 3 29 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 86 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 86 105 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 85 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 105 192 3 28 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 83 105 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  82 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 81 105 192 3 27 35 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 80 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 80 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 79 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 105 192 3 26 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 77
  105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 76 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 192 3 25 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 74 105 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  73 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 192 3 24 35 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 71 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 70 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 105 192 3 23 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 68
  105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 192 3 22 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 105 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  64 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 192 3 21 35 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 62 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 192 3 20 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 105 192 3 19 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 105 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  55 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 105 192 3 18 35 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 192 3 17 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 50
  105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 105 192 3 16 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 105 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 192 3 15 35 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 192 3 14 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 105 192 3 13 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 105 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  37 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 192 3 12 35 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 192 3 11 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 192 3 10 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 105 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 192 3 9 35 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 192 3 8 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 105 192 3 7 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 105 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 192 3 6 35 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 192 3 5 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 105 192 3 4 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 105 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 192 3 3 35 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 192
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 192 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 192 3 2 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 192 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 105 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 192
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 105 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 192 3 1 35 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 192 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 105 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 192 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 105 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 104 192
  (Eq.refl Bool.true) (allA_succ_of_gcd 88 104 192 8 11 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 104 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 87 104 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 104 192 2 43 52 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 104 192 (accept_3_4 85
  104 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 104 192 4 21 26 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 104 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 83 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 104 192 2 41 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 104 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 81 104 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 104 192 8 10 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 104 192 (accept_3_4 79 104 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 104 192 2 39 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 104 192 (Polychromatic418967fa.accept_10_7_4_2_1_903
  77 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 104 192 4 19 26 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 104 192
  (Polychromatic418967fa.accept_18_3_14_12_1_1141 75 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 104 192 2 37 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 104 192 (accept_3_4 73 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 104 192 8 9 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 104 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 71 104 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 104 192 2 35 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 104 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 69
  104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 104 192 4 17 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 104 192 (accept_3_4 67
  104 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 104 192 2 33 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 104 192
  (Polychromatic418967fa.accept_7_2_6_3_1_100 65 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 104 192 8 8 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 104 192 (Polychromatic418967fa.accept_25_13_4_17_1_11149 63 104 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 104 192 2 31 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 104 192 (accept_3_4 61 104 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 104 192 4 15 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 104 192 (Polychromatic418967fa.accept_14_3_6_10_1_752
  59 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 104 192 2 29 52 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 104 192
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 104 192 8 7 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 104 192 (accept_3_4 55 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  104 192 2 27 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 104 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 53 104 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 104 192 4 13 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 104 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 51
  104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 104 192 2 25 52 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 104 192 (accept_3_4 49
  104 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 104 192 8 6 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 104 192
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 104 192 2 23 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 104 192 (Polychromatic418967fa.accept_14_3_6_10_1_752 45 104 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 104 192 4 11 26 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 104 192 (accept_3_4 43 104 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 104 192 2 21 52 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 104 192
  (Polychromatic418967fa.accept_15_11_14_12_1_2458 41 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 104 192 8 5 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 104 192 (Polychromatic418967fa.accept_7_4_6_3_1_271 39 104 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 104 192 2 19 52 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 104 192 (accept_3_4 37 104 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 104 192 4 9 26 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 104 192
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 104 192 2 17 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 104 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 104 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 104 192 8 4 13 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 104 192 (accept_3_4 31 104 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 104 192 2 15 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 104 192 (Polychromatic418967fa.accept_9_2_5_3_1_37 29
  104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 104 192 4 7 26 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 104 192
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 104 192 2 13 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 104 192 (accept_3_4 25 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 104 192 8 3 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 104 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 23 104 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 104 192 2 11 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 104 192
  (Polychromatic418967fa.accept_18_3_14_12_1_1141 21 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 104 192 4 5 26 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 104 192 (accept_3_4 19 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 104 192 2 9 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 104 192 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 104 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 104 192 8 2 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 104 192 (Polychromatic418967fa.accept_9_6_5_3_1_205 15
  104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 104 192 2 7 52 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 104 192 (accept_3_4 13
  104 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 104 192 4 3 26 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 104 192
  (Polychromatic418967fa.accept_7_4_6_3_1_271 11 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 104 192 2 5 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 9 104 192 (Polychromatic418967fa.accept_7_2_6_3_1_100 9 104 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 104 192 8 1 13 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 104 192 (accept_3_4 7 104 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 6 104 192 2 3 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 104 192 (Polychromatic418967fa.accept_25_5_4_17_1_11148 5 104 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 104 192 4 1 26 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 104 192
  (Polychromatic418967fa.accept_14_3_6_10_1_752 3 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 104 192 2 1 52 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 104 192 (accept_3_4 1 104 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 104
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 90 103 192
  (Eq.refl Bool.true) (allA_succ_of_accept 89 103 192 (accept_3_5 89 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 103 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 88 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 103 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 87 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 103 192 (accept_3_5 86 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 103 192 (Polychromatic418967fa.accept_7_1_5_3_1_268
  85 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 103 192
  (Polychromatic418967fa.accept_13_6_12_10_1_690 84 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 83 103 192 (accept_3_5 83 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  82 103 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 82 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 103 192 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 103 192 (accept_3_5 80 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 103 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 79 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 78 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 103 192 (accept_3_5 77 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 103 192 (Polychromatic418967fa.accept_11_10_4_5_1_359 76 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 103 192 (Polychromatic418967fa.accept_10_5_3_2_1_899 75 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 192 (accept_3_5 74 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 73 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 72 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 103 192 (accept_3_5 71 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  70 103 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 103 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 69 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 192 (accept_3_5 68 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 192 (Polychromatic418967fa.accept_13_2_12_10_1_2649 67 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 192
  (Polychromatic418967fa.accept_23_20_11_8_1_7798 66 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 103 192 (accept_3_5 65 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 103 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 64 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 103 192 (Polychromatic418967fa.accept_13_11_12_10_1_2652 63
  103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 192 (accept_3_5 62
  103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 192
  (Polychromatic418967fa.accept_9_7_4_3_1_204 61 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 103 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 103 192 (accept_3_5 59 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 103 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 58 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 103 192 (Polychromatic418967fa.accept_7_1_5_3_1_268
  57 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 192 (accept_3_5 56
  103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 192
  (Polychromatic418967fa.accept_9_1_4_3_1_201 55 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 103 192 (Polychromatic418967fa.accept_11_10_4_5_1_359 54 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 103 192 (accept_3_5 53 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 103 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 103 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 51
  103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 192 (accept_3_5 50
  103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 192
  (Polychromatic418967fa.accept_19_11_8_2_1_2847 49 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 103 192 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 103 192 (accept_3_5 47 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 103 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 103 192 (Polychromatic418967fa.accept_10_5_3_2_1_899
  45 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 192 (accept_3_5 44
  103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 43 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 103 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 103 192 (accept_3_5 41 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 103 192 (Polychromatic418967fa.accept_14_12_5_10_1_2130 40 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 103 192
  (Polychromatic418967fa.accept_18_3_13_12_1_1138 39 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 103 192 (accept_3_5 38 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 103 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 37 103 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 36 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 103 192 (accept_3_5 35 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 103 192 (Polychromatic418967fa.accept_9_7_4_3_1_204
  34 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 103 192
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 103 192 (accept_3_5 32 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 103 192 (Polychromatic418967fa.accept_10_1_3_2_1_220 31 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 103 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 30 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 103 192 (accept_3_5 29 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 103 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 103 192
  (Polychromatic418967fa.accept_21_6_19_3_1_4823 27 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 103 192 (accept_3_5 26 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 103 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 103 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 103 192 (accept_3_5 23 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 103 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 22 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 103 192
  (Polychromatic418967fa.accept_10_1_3_2_1_220 21 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 103 192 (accept_3_5 20 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 103 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 103 192 (Polychromatic418967fa.accept_15_3_13_12_1_348 18 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 103 192 (accept_3_5 17 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 103 192 (Polychromatic418967fa.accept_7_2_5_3_1_98 16 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 103 192
  (Polychromatic418967fa.accept_7_1_5_3_1_268 15 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 103 192 (accept_3_5 14 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 103 192 (Polychromatic418967fa.accept_19_13_8_2_1_4089 13 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 103 192 (Polychromatic418967fa.accept_14_12_5_10_1_2130 12 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 103 192 (accept_3_5 11 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 103 192 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 103 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 192
  (Polychromatic418967fa.accept_7_2_5_3_1_98 9 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 103 192 (accept_3_5 8 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  103 192 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 103 192 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 103 192 (accept_3_5 5 103 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 103 192 (Polychromatic418967fa.accept_17_4_1_5_1_2554 4 103 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 103 192
  (Polychromatic418967fa.accept_15_3_13_12_1_348 3 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 103 192 (accept_3_5 2 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  103 192 (Polychromatic418967fa.accept_7_1_5_3_1_268 1 103 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 103
  192)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 102 192
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 102 192 6 15 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 102 192 (Polychromatic418967fa.accept_19_13_7_2_1_5413 89 102
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 102 192 2 44 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 87 102 192 3 29 34 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 86 102 192 2 43 51
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 102 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 85 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 102 192 6 14 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 102 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 83 102 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 102 192 2 41 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 81 102 192 3 27 34 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 80 102 192 2 40 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 102 192
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 79 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 78 102 192 6 13 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 102 192 (Polychromatic418967fa.accept_13_12_11_10_1_2711 77 102 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 102 192 2 38 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 75 102 192 3 25 34 64
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 74 102 192 2 37 51
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 102 192
  (Polychromatic418967fa.accept_13_8_11_10_1_636 73 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 102 192 6 12 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 102 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 71 102 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 102 192 2 35 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 69 102 192 3 23 34 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 68 102 192 2 34 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 102 192
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 67 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 66 102 192 6 11 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 65 102 192 (Polychromatic418967fa.accept_21_2_18_3_1_9697 65 102 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 102 192 2 32 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 63 102 192 3 21 34 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 62 102 192 2 31 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 102 192
  (Polychromatic418967fa.accept_19_4_7_2_1_6944 61 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 102 192 6 10 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 102 192 (Polychromatic418967fa.accept_20_19_2_12_1_2516 59 102 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 102 192 2 29 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 57 102 192 3 19 34 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 56 102 192 2 28 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 102 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 55 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 102 192 6 9 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 102 192 (Polychromatic418967fa.accept_13_1_11_10_1_1258 53 102 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 102 192 2 26 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 102 192 3 17 34 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 102 192 2 25 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 102 192
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 49 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 192 6 8 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 102 192 (Polychromatic418967fa.accept_13_8_11_10_1_636 47 102 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 102 192 2 23 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 45 102 192 3 15 34 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 44 102 192 2 22 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 102 192
  (Polychromatic418967fa.accept_7_1_4_3_1_21 43 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 102 192 6 7 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 102 192 (Polychromatic418967fa.accept_7_6_4_3_1_266 41 102 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 102 192 2 20 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 102 192 3 13 34 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 102 192 2 19 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 102 192
  (Polychromatic418967fa.accept_20_17_2_12_1_8168 37 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 102 192 6 6 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 102 192 (Polychromatic418967fa.accept_14_7_4_10_1_1351 35 102 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 102 192 2 17 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 102 192 3 11 34 64 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 102 192 2 16 51 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 102 192
  (Polychromatic418967fa.accept_21_10_18_3_1_11147 31 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 102 192 6 5 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 102 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 29 102 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 102 192 2 14 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 102 192 3 9 34 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 102 192 2 13 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 102 192
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 25 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 102 192 6 4 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 102 192 (Polychromatic418967fa.accept_19_4_7_2_1_6944 23 102 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 102 192 2 11 51 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 102 192 3 7 34 64 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 102 192 2 10 51 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 102 192
  (Polychromatic418967fa.accept_11_8_3_5_1_355 19 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 102 192 6 3 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 102 192 (Polychromatic418967fa.accept_13_4_11_10_1_1226 17 102 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 102 192 2 8 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 102 192 3 5 34 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 102 192 2 7 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 102 192
  (Polychromatic418967fa.accept_7_6_4_3_1_266 13 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 102 192 6 2 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 102 192 (Polychromatic418967fa.accept_21_11_18_3_1_4862 11 102 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 102 192 2 5 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 102 192 3 3 34 64 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 102 192 2 4 51 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 102 192
  (Polychromatic418967fa.accept_14_7_4_10_1_1351 7 102 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 192 6 1 17 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 192 (Polychromatic418967fa.accept_19_5_7_2_1_1728 5 102 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 102 192 2 2 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 102 192 3 1 34 64 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 102 192 2 1 51 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 102 192 (Polychromatic418967fa.accept_7_1_4_3_1_21 1 102 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 102
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 101 192
  (Eq.refl Bool.true) (allA_succ_of_accept 91 101 192 (accept_3_4 91 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 101 192 (Polychromatic418967fa.accept_14_6_3_10_1_3905 90 101 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 101 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 89 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 101 192 (accept_3_4 88 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771
  87 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 101 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 86 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 101 192 (accept_3_4 85 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 101 192 (Polychromatic418967fa.accept_19_8_6_2_1_11146 84 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 101 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 83 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 101 192 (accept_3_4 82 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 101 192 (Polychromatic418967fa.accept_18_9_11_12_1_5727 81 101
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 80 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 101 192 (accept_3_4 79 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 78 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 101 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 77 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 101 192 (accept_3_4 76 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 101 192 (Polychromatic418967fa.accept_21_12_17_3_1_11145 75 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 101 192
  (Polychromatic418967fa.accept_11_8_2_5_1_1769 74 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 101 192 (accept_3_4 73 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 101 192 (Polychromatic418967fa.accept_17_4_16_5_1_8635 72 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 101 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 71 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 101 192 (accept_3_4 70 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 101 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 68 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 101 192 (accept_3_4 67 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 101 192 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 101 192 (Polychromatic418967fa.accept_19_8_6_2_1_11146 65 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 101 192 (accept_3_4 64 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 101 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 101
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 101 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 62 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 101 192 (accept_3_4 61 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 101 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 101 192 (accept_3_4 58 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 101 192 (Polychromatic418967fa.accept_21_15_17_3_1_3373 57 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 101 192
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 101 192 (accept_3_4 55 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 101 192 (Polychromatic418967fa.accept_21_12_17_3_1_11145 54 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 101 192 (accept_3_4 52 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 101 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 101 192 (accept_3_4 49 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 101 192 (Polychromatic418967fa.accept_14_6_3_10_1_3905 48 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 101 192 (Polychromatic418967fa.accept_22_3_13_16_1_11144 47 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 101 192 (accept_3_4 46 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 101 192 (Polychromatic418967fa.accept_17_11_16_5_1_3612 45 101
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 101 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 101 192 (accept_3_4 43 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 101 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 101 192 (accept_3_4 40 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 101 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 39 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 101 192
  (Polychromatic418967fa.accept_15_8_11_12_1_1626 38 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 101 192 (accept_3_4 37 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 101 192 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 101 192 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 101 192 (accept_3_4 34 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771
  33 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 101 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 101 192 (accept_3_4 31 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 101 192 (Polychromatic418967fa.accept_11_8_2_5_1_1769 30 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 101 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 101 192 (accept_3_4 28 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 101 192 (Polychromatic418967fa.accept_14_13_3_10_1_2159 27 101
  192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 101 192 (accept_3_4 25 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 101 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 101 192 (accept_3_4 22 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 101 192 (Polychromatic418967fa.accept_14_7_3_10_1_1364 21 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 101 192
  (Polychromatic418967fa.accept_14_6_3_10_1_3905 20 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 101 192 (accept_3_4 19 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 101 192 (Polychromatic418967fa.accept_17_1_16_5_1_3670 18 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 101 192 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 101 192 (accept_3_4 16 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 101 192
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 101 192 (accept_3_4 13 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 101 192 (Polychromatic418967fa.accept_19_12_6_2_1_5424 12 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 101 192 (Polychromatic418967fa.accept_17_11_16_5_1_3612 11 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 101 192 (accept_3_4 10 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 101 192 (Polychromatic418967fa.accept_10_9_1_2_1_522 9 101 192
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 101 192
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 101 192 (accept_3_4 7 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  101 192 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 101 192 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 101 192 (accept_3_4 4 101 192 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 101 192 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 101 192 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 101 192
  (Polychromatic418967fa.accept_17_2_16_5_1_1584 2 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 101 192 (accept_3_4 1 101 192 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 101
  192))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_192_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


