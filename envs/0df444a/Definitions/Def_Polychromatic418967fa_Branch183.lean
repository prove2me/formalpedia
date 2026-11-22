-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch183
-- name    : Polychromatic418967fa_Branch183
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:20:21.90918+00:00
-- url     : https://prove2.me/theorems/45318a5f-6f79-4a32-9451-68387b238e02
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch183_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_183 : allB 183 183 :=
  allB_succ' 2 182 183 (Eq.refl Bool.true) (allA_succ_of_accept 1 182 183 (accept_3_4 1 182 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 182 183)) (allB_succ' 3 181 183 (Eq.refl Bool.true) (allA_succ_of_accept 2 181 183
  (accept_3_5 2 181 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 183
  (Polychromatic418967fa.accept_25_1_6_8_1_10568 1 181 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 181 183))) (allB_succ' 4 180 183 (Eq.refl Bool.true) (allA_succ_of_gcd 3 180 183 3 1 60 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 180 183
  (Polychromatic418967fa.accept_19_2_9_12_1_2237 2 180 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 180 183 (Polychromatic418967fa.accept_19_1_9_12_1_6207 1 180 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 183)))) (allB_succ' 5 179 183 (Eq.refl Bool.true) (allA_succ_of_accept 4
  179 183 (accept_3_4 4 179 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 179 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 179 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 179 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 183 (accept_3_4 1 179 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 179 183))))) (allB_succ' 6 178 183 (Eq.refl Bool.true) (allA_succ_of_accept 5 178 183
  (accept_3_5 5 178 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 178 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 4 178 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 178 183 (Polychromatic418967fa.accept_17_3_8_13_1_5361 3 178 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 178 183 (accept_3_5 2 178 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 178 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 178 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 183)))))) (allB_succ' 7 177 183 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 177 183 3 2 59 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 177 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 177 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 177 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 177 183 3 1 59 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 177 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 177 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 177 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177 183))))))) (allB_succ' 8 176 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 183 (accept_3_4 7 176 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  176 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 176 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 176 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 176 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 176 183 (accept_3_4 4 176 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 176 183 (Polychromatic418967fa.accept_13_3_7_1_1_334 3 176 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 176 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 176 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 176 183 (accept_3_4 1 176 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176
  183)))))))) (allB_succ' 9 175 183 (Eq.refl Bool.true) (allA_succ_of_accept 8 175 183 (accept_3_5 8 175 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 175 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 175 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 175 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 175 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 175 183 (accept_3_5 5 175 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  175 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 175 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 175 183 (Polychromatic418967fa.accept_11_3_10_7_1_129 3 175 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 183 (accept_3_5 2 175 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 175 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 175 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 183))))))))) (allB_succ' 10 174 183 (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 174 183 3 3 58 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 174 183 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 174 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 174 183 (Polychromatic418967fa.accept_10_7_4_3_1_560 7
  174 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174 183 3 2 58 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 174 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 174 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 174 183 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 174 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 174 183 3 1 58 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 174 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 174 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 174 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 174 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 174 183)))))))))) (allB_succ' 11 173 183 (Eq.refl Bool.true) (allA_succ_of_accept 10 173 183 (accept_3_4 10
  173 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 183
  (Polychromatic418967fa.accept_12_9_5_3_1_782 9 173 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 173 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 173 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 173 183 (accept_3_4 7 173 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 173 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 173 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 173 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 5
  173 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 183 (accept_3_4 4 173
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 183 (Polychromatic418967fa.accept_7_3_5_1_1_72
  3 173 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 173 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 183 (accept_3_4 1 173 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  183))))))))))) (allB_succ' 12 172 183 (Eq.refl Bool.true) (allA_succ_of_accept 11 172 183 (accept_3_5 11 172 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 172 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 10
  172 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 172 183
  (Polychromatic418967fa.accept_19_9_1_12_1_6234 9 172 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 172 183 (accept_3_5 8 172 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  172 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 172 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 172 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 172 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 172 183 (accept_3_5 5 172 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 172 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 172 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 172 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 172 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 172 183 (accept_3_5 2 172 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  172 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 172 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 172 183)))))))))))) (allB_succ' 13 171 183 (Eq.refl Bool.true) (allA_succ_of_gcd 12 171 183 3 4
  57 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 171 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 183 (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 171 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 183 3 3 57 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 183 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 171 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 183
  (Polychromatic418967fa.accept_18_7_9_3_1_800 7 171 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 171 183 3 2 57 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 171 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 171 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 171 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 171 183 3 1 57 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 171 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 171 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 171 183 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 171 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 171 183))))))))))))) (allB_succ' 14 170 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 13 170 183 (accept_3_4 13 170 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 170 183 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 170 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 170 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 170 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 170 183 (accept_3_4 10 170 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 170 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 170 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 170 183
  (Polychromatic418967fa.accept_14_8_2_1_1_1652 8 170 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 170 183 (accept_3_4 7 170 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  170 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 170 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 170 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 170 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 170 183 (accept_3_4 4 170 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 170 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 170 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 170 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 170 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 170 183 (accept_3_4 1 170 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  183)))))))))))))) (allB_succ' 15 169 183 (Eq.refl Bool.true) (allA_succ_of_accept 14 169 183 (accept_3_5 14 169 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 169 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 13
  169 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 169 183
  (Polychromatic418967fa.accept_17_12_16_13_1_7951 12 169 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 169 183 (accept_3_5 11 169 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 169 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 169 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 183 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 169 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 169 183 (accept_3_5 8 169 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 169 183 (Polychromatic418967fa.accept_15_7_4_3_1_1930
  7 169 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 169 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 169 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 169 183 (accept_3_5 5 169 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  169 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 169 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 169 183 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 169 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 169 183 (accept_3_5 2 169 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 169 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 169 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 169 183))))))))))))))) (allB_succ' 16 168 183 (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 168 183 3 5 56 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 168 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 168 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 168 183 (Polychromatic418967fa.accept_9_4_6_3_1_179
  13 168 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 183 3 4 56 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 183
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 168 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 168 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 168 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 168 183 3 3 56 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 168 183 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 168 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 168 183
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 168 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 168 183 3 2 56 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 168 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 168 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 168 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 168 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 168 183 3 1 56 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 168 183
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 168 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 168 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 168 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168 183)))))))))))))))) (allB_succ' 17 167 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 16 167 183 (accept_3_4 16 167 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 167 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 167 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 167 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 167 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 167 183 (accept_3_4 13 167 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 167 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 167 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 167 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 167 183 (accept_3_4 10 167 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  167 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 167 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 167 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 167 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 167 183 (accept_3_4 7 167 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 167 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 167 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 167 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 167 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 167 183 (accept_3_4 4 167 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  167 183 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 167 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 167 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 167 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 167 183 (accept_3_4 1 167 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 167 183))))))))))))))))) (allB_succ' 18 166 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 166 183 (accept_3_5 17 166 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 166 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 166 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 166 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 166 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 166 183 (accept_3_5 14 166 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 166 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 166 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 166 183
  (Polychromatic418967fa.accept_21_12_19_15_1_8942 12 166 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 166 183 (accept_3_5 11 166 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 166 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 166 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 166 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 166 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 166 183 (accept_3_5 8 166 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 166 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7
  166 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 166 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 166 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 166 183 (accept_3_5 5 166 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  166 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 166 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 166 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 166 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 166 183 (accept_3_5 2 166 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 166 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 166 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 183)))))))))))))))))) (allB_succ' 19 165 183
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 165 183 3 6 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 165 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 165 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 165 183
  (Polychromatic418967fa.accept_17_16_12_13_1_3070 16 165 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 165 183 3 5 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 165 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 165 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 183
  (Polychromatic418967fa.accept_12_1_9_3_1_370 13 165 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 165 183 3 4 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 165 183 (Polychromatic418967fa.accept_12_11_9_3_1_792 11 165 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 165 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 165 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 165 183 3 3 55 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 183
  (Polychromatic418967fa.accept_10_8_5_3_1_543 8 165 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 183 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 165 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 183 3 2 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 165 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 165 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 165 183
  (Polychromatic418967fa.accept_14_4_11_1_1_940 4 165 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 165 183 3 1 55 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 165 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 165 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 165 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 165 183))))))))))))))))))) (allB_succ' 20 164
  183 (Eq.refl Bool.true) (allA_succ_of_accept 19 164 183 (accept_3_4 19 164 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 164 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 164 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 164 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 17
  164 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 164 183 (accept_3_4 16
  164 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 164 183
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 164 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 164 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 164 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 164 183 (accept_3_4 13 164 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 164 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 164 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 164 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  164 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 164 183 (accept_3_4 10
  164 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 164 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 164 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 164 183 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 164 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 164 183 (accept_3_4 7 164 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 164 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 164 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 164 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 5
  164 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 164 183 (accept_3_4 4 164
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 164 183
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 164 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 164 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 164 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 164 183 (accept_3_4 1 164 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 164 183)))))))))))))))))))) (allB_succ' 21 163 183 (Eq.refl Bool.true) (allA_succ_of_accept 20
  163 183 (accept_3_5 20 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 163 183
  (Polychromatic418967fa.accept_13_6_7_1_1_335 19 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 163 183 (Polychromatic418967fa.accept_19_18_11_12_1_6163 18 163 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 163 183 (accept_3_5 17 163 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 163 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 163 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 163 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 163 183 (accept_3_5 14 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 163 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 163 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 163 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 163 183 (accept_3_5 11 163 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 163 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 163 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 163 183
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 163 183 (accept_3_5 8 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  163 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 163 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 163 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 163 183 (accept_3_5 5 163 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 163 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 163 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 163 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 163 183 (accept_3_5 2 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  163 183 (Polychromatic418967fa.accept_15_1_13_3_1_2002 1 163 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 163 183))))))))))))))))))))) (allB_succ' 22 162 183 (Eq.refl Bool.true) (allA_succ_of_gcd 21 162
  183 3 7 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20
  162 183 (Polychromatic418967fa.accept_12_8_6_3_1_366 20 162 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 162 183 (Polychromatic418967fa.accept_20_19_2_3_1_4486 19 162 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 162 183 3 6 54 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 162 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 162 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 162 183 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 162 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 162 183 3 5 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 162 183 (Polychromatic418967fa.accept_12_2_6_3_1_331
  14 162 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 162 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 162 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 183 3 4 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 162 183 (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 162 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 162 183 (Polychromatic418967fa.accept_12_10_6_3_1_786 10 162
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 162 183 3 3 54 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 162 183
  (Polychromatic418967fa.accept_12_8_6_3_1_366 8 162 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 162 183 (Polychromatic418967fa.accept_13_7_6_1_1_368 7 162 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162 183 3 2 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 162 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 162 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 162 183
  (Polychromatic418967fa.accept_11_4_8_7_1_819 4 162 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 162 183 3 1 54 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 162 183 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 162 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 162 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 162 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 183)))))))))))))))))))))) (allB_succ' 23
  161 183 (Eq.refl Bool.true) (allA_succ_of_accept 22 161 183 (accept_3_4 22 161 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 161 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 161 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 183 (accept_3_4 19 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 183 (Polychromatic418967fa.accept_13_4_5_1_1_833 17 161 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 183 (accept_3_4 16 161 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 161 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 183 (accept_3_4 13 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 183 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 183 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 161 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 183 (accept_3_4 10 161 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 161 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 183 (accept_3_4 7 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 183 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 161 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 183 (accept_3_4 4 161 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 183 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 161 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 183 (accept_3_4 1 161 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  183))))))))))))))))))))))) (allB_succ' 24 160 183 (Eq.refl Bool.true) (allA_succ_of_accept 23 160 183 (accept_3_5 23
  160 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 160 183
  (Polychromatic418967fa.accept_9_4_7_3_1_43 22 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 160 183 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 160 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 160 183 (accept_3_5 20 160 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 160 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 160 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 160 183 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 160 183 (accept_3_5 17
  160 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 160 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 160 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 160 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 160 183 (accept_3_5 14 160 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 160 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 160 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 160 183 (Polychromatic418967fa.accept_7_5_6_1_1_407
  12 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 160 183 (accept_3_5 11
  160 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 160 183
  (Polychromatic418967fa.accept_9_1_7_3_1_41 10 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 160 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 160 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 160 183 (accept_3_5 8 160 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 160 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 160 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 160 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 6
  160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 160 183 (accept_3_5 5 160
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 160 183 (Polychromatic418967fa.accept_9_4_7_3_1_43
  4 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 160 183
  (Polychromatic418967fa.accept_13_3_4_1_1_363 3 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 160 183 (accept_3_5 2 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  160 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 160 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 160 183)))))))))))))))))))))))) (allB_succ' 25 159 183 (Eq.refl Bool.true) (allA_succ_of_gcd 24
  159 183 3 8 53 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  23 159 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 159 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 159 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 159 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 159 183 3 7 53 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 159 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 159 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 159 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 159 183 3 6 53 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 159 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  159 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 183
  (Polychromatic418967fa.accept_9_7_6_3_1_456 16 159 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 159 183 3 5 53 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 159 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 159 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 159 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 159 183 3 4 53 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 159 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 159 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 159 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 159 183 3 3 53 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 159 183 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 159 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 183
  (Polychromatic418967fa.accept_9_7_6_3_1_456 7 159 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 159 183 3 2 53 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 159 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 159 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 159 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 159 183 3 1 53 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 159 183
  (Polychromatic418967fa.accept_9_2_6_3_1_178 2 159 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 159 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 159 183))))))))))))))))))))))))) (allB_succ' 26 158 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 25 158 183 (accept_3_4 25 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 158 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 158 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 158 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 158 183 (accept_3_4 22 158 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 158 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 158 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 158 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 158 183 (accept_3_4 19 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 158 183 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 158 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 158 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 158 183 (accept_3_4 16 158 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 158 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 158 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 158 183
  (Polychromatic418967fa.accept_11_3_4_7_1_114 14 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 158 183 (accept_3_4 13 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 158 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 158 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 158 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 158 183 (accept_3_4 10 158 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 158 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 158 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 158 183
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 158 183 (accept_3_4 7 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  158 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 158 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 158 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 158 183 (accept_3_4 4 158 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 158 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 158 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 158 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 158 183 (accept_3_4 1 158 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  183)))))))))))))))))))))))))) (allB_succ' 27 157 183 (Eq.refl Bool.true) (allA_succ_of_accept 26 157 183 (accept_3_5
  26 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 157 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 157 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 157 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 157 183 (accept_3_5 23 157 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 157 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 157 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 157 183
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 157 183 (accept_3_5 20 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 157 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 157 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 157 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 157 183 (accept_3_5 17 157 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 157 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 157 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 157 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 157 183 (accept_3_5 14 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 157 183 (Polychromatic418967fa.accept_19_13_5_12_1_6107 13 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 157 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 157 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 157 183 (accept_3_5 11 157 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 157 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 157 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 157 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 157 183 (accept_3_5 8 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  157 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 157 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 157 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 157 183 (accept_3_5 5 157 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 157 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 157 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 157 183
  (Polychromatic418967fa.accept_17_3_4_13_1_2030 3 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 157 183 (accept_3_5 2 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  157 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 157 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 157 183))))))))))))))))))))))))))) (allB_succ' 28 156 183 (Eq.refl Bool.true) (allA_succ_of_gcd
  27 156 183 3 9 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 156 183 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 156 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 156 183 (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 156
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 183 3 8 52 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 183
  (Polychromatic418967fa.accept_21_2_9_15_1_5747 23 156 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 156 183 (Polychromatic418967fa.accept_14_8_2_1_1_1652 22 156 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 156 183 3 7 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 156 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  156 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 156 183
  (Polychromatic418967fa.accept_8_3_4_7_1_475 19 156 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 183 3 6 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 156 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 156 183 (Polychromatic418967fa.accept_15_1_6_3_1_2827 16 156
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 156 183 3 5 52 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 156 183
  (Polychromatic418967fa.accept_18_14_12_3_1_5103 14 156 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 156 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 156 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 183 3 4 52 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 183
  (Polychromatic418967fa.accept_8_3_4_7_1_475 11 156 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 156 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 156 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 156 183 3 3 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 156 183 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 156 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 156 183
  (Polychromatic418967fa.accept_10_7_6_3_1_927 7 156 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 156 183 3 2 52 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 156 183 (Polychromatic418967fa.accept_15_5_6_3_1_525 5 156 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 156 183 (Polychromatic418967fa.accept_16_4_12_7_1_4475 4 156
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 156 183 3 1 52 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 156 183
  (Polychromatic418967fa.accept_16_2_12_7_1_3410 2 156 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 156 183 (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 156 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 156 183)))))))))))))))))))))))))))) (allB_succ' 29 155 183 (Eq.refl
  Bool.true) (allA_succ_of_accept 28 155 183 (accept_3_4 28 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 155 183 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 155 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 155 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 155 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 183 (accept_3_4 25 155 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 183 (Polychromatic418967fa.accept_9_6_2_3_1_771
  24 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 183 (accept_3_4 22 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 155 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 183 (accept_3_4 19 155 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 183 (Polychromatic418967fa.accept_10_8_5_3_1_543 18 155 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 183 (accept_3_4 16 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 155 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 183 (accept_3_4 13 155 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 155 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 183
  (Polychromatic418967fa.accept_13_11_12_1_1_2154 11 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 155 183 (accept_3_4 10 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 155 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 155 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 155 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 183 (accept_3_4 7 155 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 6
  155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 5 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 183 (accept_3_4 4 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 183 (Polychromatic418967fa.accept_16_3_11_7_1_770 3 155 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 155 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 183 (accept_3_4 1 155 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 183))))))))))))))))))))))))))))) (allB_succ' 30 154 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 29 154 183 (accept_3_5 29 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 154 183 (Polychromatic418967fa.accept_19_9_2_12_1_6243 28 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 154 183 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 154 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 154 183 (accept_3_5 26 154 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 154 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 154 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 154 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 154 183 (accept_3_5 23 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 154 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 154 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 154 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 154 183 (accept_3_5 20 154 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 154 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 154 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 154 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 154 183 (accept_3_5 17 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 154 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 154 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 154 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 154 183 (accept_3_5 14 154 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 154 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 154 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 154 183
  (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 154 183 (accept_3_5 11 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 154 183 (Polychromatic418967fa.accept_13_10_11_1_1_2152 10 154 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 154 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9
  154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 154 183 (accept_3_5 8 154
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 154 183 (Polychromatic418967fa.accept_6_1_4_3_1_14
  7 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 154 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 154 183 (accept_3_5 5 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  154 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 154 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 154 183 (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 154 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 154 183 (accept_3_5 2 154 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 154 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 154 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 154 183))))))))))))))))))))))))))))))
  (allB_succ' 31 153 183 (Eq.refl Bool.true) (allA_succ_of_gcd 30 153 183 3 10 51 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 153 183
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 153 183 (Polychromatic418967fa.accept_19_9_1_12_1_6234 28 153 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 153 183 3 9 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 153 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 183
  (Polychromatic418967fa.accept_11_3_10_7_1_129 25 153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 153 183 3 8 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 153 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 153 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 153 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 153 183 3 7 51 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 153 183
  (Polychromatic418967fa.accept_18_2_9_3_1_3825 20 153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 153 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 153 183 3 6 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 153 183 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 153 183 3 5 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 153 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 153 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 153
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 153 183 3 4 51 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 153 183
  (Polychromatic418967fa.accept_12_11_9_3_1_792 11 153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 153 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 153 183 3 3 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 153 183 (Polychromatic418967fa.accept_16_8_9_7_1_768 8 153 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 183
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 153 183 3 2 51 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 153 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 153 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 183 (Polychromatic418967fa.accept_13_4_10_1_1_1390 4 153
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 153 183 3 1 51 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 153 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 153 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 153 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153 183))))))))))))))))))))))))))))))) (allB_succ' 32 152 183 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 183 (accept_3_4 31 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 152 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 152 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 152 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 152 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 152 183 (accept_3_4 28 152 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 152 183 (Polychromatic418967fa.accept_7_6_5_1_1_416
  27 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 152 183
  (Polychromatic418967fa.accept_17_9_16_13_1_6636 26 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 152 183 (accept_3_4 25 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 152 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 152 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 152 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 152 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 152 183 (accept_3_4 22 152 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 152 183 (Polychromatic418967fa.accept_10_1_2_3_1_1910
  21 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 152 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 152 183 (accept_3_4 19 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 152 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 152 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 152 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 152 183 (accept_3_4 16 152 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 152 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 152 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 152 183
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 152 183 (accept_3_4 13 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 152 183 (Polychromatic418967fa.accept_15_12_2_3_1_1146 12 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 152 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 152 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 152 183 (accept_3_4 10 152 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 152 183 (Polychromatic418967fa.accept_16_9_8_7_1_4529 9 152 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 152 183
  (Polychromatic418967fa.accept_13_8_9_1_1_2147 8 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 152 183 (accept_3_4 7 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  152 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 152 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 152 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 152 183 (accept_3_4 4 152 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 152 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 152 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 152 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 152 183 (accept_3_4 1 152 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  183)))))))))))))))))))))))))))))))) (allB_succ' 33 151 183 (Eq.refl Bool.true) (allA_succ_of_accept 32 151 183
  (accept_3_5 32 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 151 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 151 183 (Polychromatic418967fa.accept_18_12_7_3_1_2666 30 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 151 183 (accept_3_5 29 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 151 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 151 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 151 183 (Polychromatic418967fa.accept_18_9_7_3_1_3871
  27 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 151 183 (accept_3_5 26
  151 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 151 183
  (Polychromatic418967fa.accept_13_12_8_1_1_825 25 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 151 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 151 183 (accept_3_5 23 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 151 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 151 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 151 183 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  21 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 151 183 (accept_3_5 20
  151 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 151 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 19 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 151 183 (Polychromatic418967fa.accept_10_8_1_3_1_1374 18 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 151 183 (accept_3_5 17 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 151 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 151 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 151 183 (Polychromatic418967fa.accept_9_6_7_3_1_436
  15 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 151 183 (accept_3_5 14
  151 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 151 183
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 151 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 151 183 (accept_3_5 11 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 151 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 151 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 151 183 (Polychromatic418967fa.accept_12_9_7_3_1_1309
  9 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 151 183 (accept_3_5 8
  151 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 151 183
  (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 151 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 151 183 (accept_3_5 5 151 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 151 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 151 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 151 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 3
  151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 151 183 (accept_3_5 2 151
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 151 183 (Polychromatic418967fa.accept_9_1_7_3_1_41
  1 151 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 151
  183))))))))))))))))))))))))))))))))) (allB_succ' 34 150 183 (Eq.refl Bool.true) (allA_succ_of_gcd 33 150 183 3 11 50
  61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 150 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 150 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 150 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 150 183 3 10 50 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 150 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 150 183
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 150 183 3 9 50 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 150 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 150 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 150 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 150 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 150 183 3 8 50 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 150 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 150 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 22 150 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 150 183 3 7 50 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 150 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 150 183
  (Polychromatic418967fa.accept_7_5_3_1_1_424 19 150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 183 3 6 50 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 150 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 150 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 150 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 150 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 150 183 3 5 50 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 150 183
  (Polychromatic418967fa.accept_9_5_6_3_1_40 14 150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 150 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 150 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 150 183 3 4 50 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 150 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 11
  150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 150 183
  (Polychromatic418967fa.accept_9_1_6_3_1_177 10 150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 150 183 3 3 50 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 150 183 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 150 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 150 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 150 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150 183 3 2 50 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 150 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 150 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 150 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 150 183 3 1 50 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 150 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 150 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 150 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 150 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 150 183)))))))))))))))))))))))))))))))))) (allB_succ' 35 149 183 (Eq.refl Bool.true) (allA_succ_of_accept 34
  149 183 (accept_3_4 34 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 183
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 149 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 149 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 183 (accept_3_4 31 149 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 149 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 149 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 183 (Polychromatic418967fa.accept_9_2_5_3_1_37 29
  149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 183 (accept_3_4 28
  149 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 183
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 149 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 149 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 183 (accept_3_4 25 149 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 149 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 149 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 183 (Polychromatic418967fa.accept_11_1_6_7_1_116
  23 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 183 (accept_3_4 22
  149 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 183
  (Polychromatic418967fa.accept_12_9_5_3_1_782 21 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 149 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 149 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 183 (accept_3_4 19 149 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 149 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 149 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 149 183 (Polychromatic418967fa.accept_7_3_2_1_1_225
  17 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 183 (accept_3_4 16
  149 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 183
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 149 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 149 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 183 (accept_3_4 13 149 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 149 183 (Polychromatic418967fa.accept_11_1_6_7_1_116 12 149 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 149 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 149 183 (accept_3_4 10 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  149 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 149 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 149 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 183 (accept_3_4 7 149 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 149 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 149 183
  (Polychromatic418967fa.accept_13_5_6_1_1_822 5 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 149 183 (accept_3_4 4 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  149 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 149 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 149 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 149 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 183 (accept_3_4 1 149 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 149 183))))))))))))))))))))))))))))))))))) (allB_succ' 36 148 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 35 148 183 (accept_3_5 35 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 148 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 148 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 148 183 (accept_3_5 32 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 148 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 148 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 148 183
  (Polychromatic418967fa.accept_12_6_4_3_1_361 30 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 148 183 (accept_3_5 29 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 148 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 148 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 148 183 (accept_3_5 26 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 148 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 148 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 148 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 24 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 148 183 (accept_3_5 23 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 148 183 (Polychromatic418967fa.accept_13_9_5_1_1_1382 22 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 148 183 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 148 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 148 183 (accept_3_5 20 148 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 148 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 148 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 148 183
  (Polychromatic418967fa.accept_12_6_4_3_1_361 18 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 148 183 (accept_3_5 17 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 148 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 148 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 148 183 (accept_3_5 14 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 148 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 148 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 148 183
  (Polychromatic418967fa.accept_13_12_5_1_1_1383 12 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 148 183 (accept_3_5 11 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 148 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 10 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 148 183 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 148 183 (accept_3_5 8 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 148 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 148 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 148 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 148 183 (accept_3_5 5 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  148 183 (Polychromatic418967fa.accept_13_4_5_1_1_833 4 148 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 148 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 3 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 148 183 (accept_3_5 2 148 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 148 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 148 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 148 183)))))))))))))))))))))))))))))))))))) (allB_succ'
  37 147 183 (Eq.refl Bool.true) (allA_succ_of_gcd 36 147 183 3 12 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 147 183 (Polychromatic418967fa.accept_10_5_7_3_1_561
  35 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 183
  (Polychromatic418967fa.accept_10_4_7_3_1_54 34 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 147 183 3 11 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 147 183 (Polychromatic418967fa.accept_15_2_12_3_1_1183 32 147 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 183
  (Polychromatic418967fa.accept_13_5_4_1_1_364 31 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 147 183 3 10 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 147 183 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 147 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 147 183 (Polychromatic418967fa.accept_8_4_3_7_1_491
  28 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 147 183 3 9 49 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 147 183
  (Polychromatic418967fa.accept_10_6_7_3_1_547 26 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 147 183 (Polychromatic418967fa.accept_10_5_7_3_1_561 25 147 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 147 183 3 8 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 147 183 (Polychromatic418967fa.accept_13_10_4_1_1_2142
  23 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 147 183
  (Polychromatic418967fa.accept_14_8_7_1_1_1615 22 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 147 183 3 7 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 147 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 147 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 183 (Polychromatic418967fa.accept_11_8_4_7_1_1303 19 147
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 147 183 3 6 49 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 147 183
  (Polychromatic418967fa.accept_15_2_12_3_1_1183 17 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 183 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 147 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 147 183 3 5 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 147 183 (Polychromatic418967fa.accept_10_4_7_3_1_54 14
  147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 183
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 13 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 147 183 3 4 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 147 183 (Polychromatic418967fa.accept_16_11_3_7_1_2375 11 147 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 147 183 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 147
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 147 183 3 3 49 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 147 183
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 8 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 147 183 (Polychromatic418967fa.accept_15_7_12_3_1_1137 7 147 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 147 183 3 2 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 147 183 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 147 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 147 183
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 147 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 147 183 3 1 49 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 147 183 (Polychromatic418967fa.accept_15_2_12_3_1_1183 2 147 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 183 (Polychromatic418967fa.accept_27_1_12_21_1_10567 1 147
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 147
  183))))))))))))))))))))))))))))))))))))) (allB_succ' 38 146 183 (Eq.refl Bool.true) (allA_succ_of_accept 37 146 183
  (accept_3_4 37 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 146 183
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 146 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 146 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 146 183 (accept_3_4 34 146 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 146 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 146 183 (Polychromatic418967fa.accept_9_5_2_3_1_194
  32 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 146 183 (accept_3_4 31
  146 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 146 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 146 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 146 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 146 183 (accept_3_4 28 146 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 146 183 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 146 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 146 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 146 183 (accept_3_4 25 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 146 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 146 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 146 183 (accept_3_4 22 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 146 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 146 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 146 183
  (Polychromatic418967fa.accept_13_7_3_1_1_814 20 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 146 183 (accept_3_4 19 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 146 183 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 146 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 146 183 (accept_3_4 16 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 146 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 146 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 146 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 146 183 (accept_3_4 13 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 146 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 146 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 146 183 (accept_3_4 10 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 146 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 146 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 146 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 146 183 (accept_3_4 7 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  146 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 146 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 146 183 (accept_3_4 4 146 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 146 183 (Polychromatic418967fa.accept_17_3_10_13_1_2021 3 146 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 146 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 146 183 (accept_3_4 1 146 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  183)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 145 183 (Eq.refl Bool.true) (allA_succ_of_accept 38 145 183
  (accept_3_5 38 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 145 183
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 145 183 (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 145 183 (accept_3_5 35 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 145 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 145 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 145 183 (Polychromatic418967fa.accept_9_6_1_3_1_191
  33 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 145 183 (accept_3_5 32
  145 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 145 183
  (Polychromatic418967fa.accept_7_3_5_1_1_72 31 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 145 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 145 183 (accept_3_5 29 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 145 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 145 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 145 183 (Polychromatic418967fa.accept_7_6_5_1_1_416
  27 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 145 183 (accept_3_5 26
  145 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 145 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 25 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 145 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 145 183 (accept_3_5 23 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 145 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 145 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 145 183 (Polychromatic418967fa.accept_12_9_1_3_1_350
  21 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 145 183 (accept_3_5 20
  145 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 145 183
  (Polychromatic418967fa.accept_13_6_2_1_1_2137 19 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 145 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 145 183 (accept_3_5 17 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 145 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 145 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 145 183 (Polychromatic418967fa.accept_9_6_1_3_1_191
  15 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 145 183 (accept_3_5 14
  145 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 145 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 145 183 (Polychromatic418967fa.accept_10_2_5_3_1_1408 12 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 145 183 (accept_3_5 11 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 145 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 145 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 145 183 (Polychromatic418967fa.accept_11_9_2_7_1_1298
  9 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 145 183 (accept_3_5 8
  145 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 145 183
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 145 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 145 183 (accept_3_5 5 145 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 145 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 145 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 145 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 3
  145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 145 183 (accept_3_5 2 145
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 145 183
  (Polychromatic418967fa.accept_20_1_5_3_1_7397 1 145 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 145 183))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 144 183 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 144 183 3 13 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 144 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 144 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 144 183 (Polychromatic418967fa.accept_10_7_4_3_1_560 37 144
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 144 183 3 12 48 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 144 183
  (Polychromatic418967fa.accept_15_5_9_3_1_528 35 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 144 183 (Polychromatic418967fa.accept_20_14_4_3_1_2006 34 144 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 144 183 3 11 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 144 183
  (Polychromatic418967fa.accept_17_15_8_13_1_6628 32 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 144 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 144 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 144 183 3 10 48 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 144 183
  (Polychromatic418967fa.accept_10_9_4_3_1_539 29 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 144 183 (Polychromatic418967fa.accept_11_6_1_7_1_1315 28 144 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 144 183 3 9 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 144 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 26
  144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 144 183
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 25 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 183 3 8 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 144 183 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 144 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 144 183 (Polychromatic418967fa.accept_17_5_8_13_1_7994 22 144
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 144 183 3 7 48 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 144 183
  (Polychromatic418967fa.accept_15_5_9_3_1_528 20 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 144 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 144 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 183 3 6 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 17
  144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 144 183
  (Polychromatic418967fa.accept_21_16_18_15_1_7282 16 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 15 144 183 3 5 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 14 144 183 (Polychromatic418967fa.accept_20_14_4_3_1_2006 14 144 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 144 183
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 183 3 4 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 144 183 (Polychromatic418967fa.accept_14_11_4_1_1_4255 11 144 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 144 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 144 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 144 183 3 3 48 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 144 183
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 144 183 (Polychromatic418967fa.accept_10_7_4_3_1_560 7 144 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144 183 3 2 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 144 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 144 183
  (Polychromatic418967fa.accept_17_4_8_13_1_7960 4 144 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 144 183 3 1 48 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 144 183 (Polychromatic418967fa.accept_21_2_18_15_1_4236 2 144 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 144 183 (Polychromatic418967fa.accept_19_1_11_12_1_6112 1 144
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  183)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 143 183 (Eq.refl Bool.true) (allA_succ_of_accept 40 143 183
  (accept_3_4 40 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 143 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 143 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 143 183 (accept_3_4 37 143 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 143 183 (Polychromatic418967fa.accept_17_2_7_13_1_4163 36 143 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 183
  (Polychromatic418967fa.accept_15_5_8_3_1_556 35 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 143 183 (accept_3_4 34 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 143 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 143 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 143 183 (accept_3_4 31 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 143 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 143 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 143 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 143 183 (accept_3_4 28 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 143 183 (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 143 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 143 183 (accept_3_4 25 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 143 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 143 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 143 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 143 183 (accept_3_4 22 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 143 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 143 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 143 183 (accept_3_4 19 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 143 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 143 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 143 183
  (Polychromatic418967fa.accept_19_17_10_12_1_6157 17 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 143 183 (accept_3_4 16 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 143 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 143 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 143 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 143 183 (accept_3_4 13 143 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 143 183 (Polychromatic418967fa.accept_7_5_3_1_1_424
  12 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 143 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 143 183 (accept_3_4 10 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  143 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 143 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 143 183 (accept_3_4 7 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 143 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 143 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 143 183
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 143 183 (accept_3_4 4 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  143 183 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 143 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 143 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 143 183 (accept_3_4 1 143 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 143 183))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 142 183 (Eq.refl
  Bool.true) (allA_succ_of_accept 41 142 183 (accept_3_5 41 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 142 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 142 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 142 183 (Polychromatic418967fa.accept_19_1_9_12_1_6207 39 142
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 142 183 (accept_3_5 38 142
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 142 183 (Polychromatic418967fa.accept_4_1_2_3_1_9
  37 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 142 183
  (Polychromatic418967fa.accept_11_3_10_7_1_129 36 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 142 183 (accept_3_5 35 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 142 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 142 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 142 183 (accept_3_5 32 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 142 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 142 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 142 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 142 183 (accept_3_5 29 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 142 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 142 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 142 183 (accept_3_5 26 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 142 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 142 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 142 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 24 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 142 183 (accept_3_5 23 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 142 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 142 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 142 183 (accept_3_5 20 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 142 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 142 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 142 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 142 183 (accept_3_5 17 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 142 183 (Polychromatic418967fa.accept_19_16_9_12_1_4792 16 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 142 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 142 183 (accept_3_5 14 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 142 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 142 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 142 183
  (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 142 183 (accept_3_5 11 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 142 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 142 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 142 183 (accept_3_5 8 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 142 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 142 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 142 183
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 142 183 (accept_3_5 5 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  142 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 142 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 142 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 142 183 (accept_3_5 2 142 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 142 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 142 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 142 183))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 43 141 183 (Eq.refl Bool.true) (allA_succ_of_gcd 42 141 183 3 14 47 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 141 183
  (Polychromatic418967fa.accept_9_5_6_3_1_40 41 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 40 141 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 141 183 3 13 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 141 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 183
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 141 183 3 12 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 141 183 (Polychromatic418967fa.accept_9_8_6_3_1_457 35 141 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 34
  141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 141 183 3 11 47 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 141 183
  (Polychromatic418967fa.accept_9_5_6_3_1_40 32 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 141 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 141 183 3 10 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 141 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 29
  141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 183
  (Polychromatic418967fa.accept_9_1_6_3_1_177 28 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 141 183 3 9 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 141 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 141 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 141 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 141 183 3 8 47 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 141 183
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 141 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 141 183 3 7 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 141 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 20
  141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 183
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 141 183 3 6 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 141 183 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 141 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 141 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 141 183 3 5 47 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 141 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 14 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 141 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 141 183 3 4 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 141 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 11
  141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 10 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 141 183 3 3 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 141 183 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 141 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 141 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 141 183 3 2 47 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 141 183
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 183 (Polychromatic418967fa.accept_9_4_6_3_1_179 4 141 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 141 183 3 1 47 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 141 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 141 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 183
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 141 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 141 183))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 140 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 140 183 (accept_3_4 43 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 140 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 140 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 140 183 (accept_3_4 40 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 140 183 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 140 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 140 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 140 183 (accept_3_4 37 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 140 183 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 140 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 140 183 (accept_3_4 34 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 140 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 140 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 140 183
  (Polychromatic418967fa.accept_15_2_5_3_1_552 32 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 140 183 (accept_3_4 31 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 140 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 140 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 140 183 (accept_3_4 28 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 140 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 140 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 140 183
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 140 183 (accept_3_4 25 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 140 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 140 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 140 183 (accept_3_4 22 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 140 183 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 140 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 140 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 140 183 (accept_3_4 19 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 140 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 140 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 140 183 (accept_3_4 16 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 140 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 140 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 140 183
  (Polychromatic418967fa.accept_17_14_4_13_1_3018 14 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 140 183 (accept_3_4 13 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 140 183 (Polychromatic418967fa.accept_18_12_14_3_1_2655 12 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 140 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11
  140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 140 183 (accept_3_4 10
  140 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 140 183
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 9 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 140 183 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 140 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 140 183 (accept_3_4 7 140 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 140 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 140 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 140 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 5
  140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 140 183 (accept_3_4 4 140
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 140 183
  (Polychromatic418967fa.accept_8_3_4_7_1_475 3 140 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 140 183 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 140 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 140 183 (accept_3_4 1 140 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 140 183)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 139 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 44 139 183 (accept_3_5 44 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 139 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 139 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 139 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 139 183 (accept_3_5 41 139 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 139 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 139 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 139 183
  (Polychromatic418967fa.accept_21_18_13_15_1_2884 39 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 139 183 (accept_3_5 38 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 139 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 139 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 139 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 139 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 139 183 (accept_3_5 35 139 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 139 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 34
  139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 139 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 139 183 (accept_3_5 32 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 139 183 (Polychromatic418967fa.accept_13_5_9_1_1_1405 31 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 139 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 139 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 139 183 (accept_3_5 29 139 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 139 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 139 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 139 183
  (Polychromatic418967fa.accept_17_10_3_13_1_6639 27 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 139 183 (accept_3_5 26 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 139 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 139 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 139 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 139 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 139 183 (accept_3_5 23 139 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 139 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 22
  139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 139 183
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 139 183 (accept_3_5 20 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 139 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 139 183 (Polychromatic418967fa.accept_13_5_9_1_1_1405 18 139 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 139 183 (accept_3_5 17 139 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 139 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 139 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 139 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 139 183 (accept_3_5 14 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 139 183 (Polychromatic418967fa.accept_19_13_6_12_1_6109 13 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 139 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 139 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 139 183 (accept_3_5 11 139 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 139 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 139 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 139 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 139 183 (accept_3_5 8 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  139 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 139 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 139 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 139 183 (accept_3_5 5 139 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 139 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 139 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 139 183
  (Polychromatic418967fa.accept_16_3_11_7_1_770 3 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 139 183 (accept_3_5 2 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  139 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 139 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 139 183))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46 138 183 (Eq.refl Bool.true)
  (allA_succ_of_gcd 45 138 183 3 15 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 138 183 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 138 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 138 183 (Polychromatic418967fa.accept_18_7_12_3_1_804
  43 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 138 183 3 14 46 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 138 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 138 183 (Polychromatic418967fa.accept_12_4_6_3_1_332 40 138 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 138 183 3 13 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 138 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 38
  138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 138 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 183 3 12 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 183 (Polychromatic418967fa.accept_10_5_8_3_1_229 35 138 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 138 183 (Polychromatic418967fa.accept_7_6_5_1_1_416
  34 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 138 183 3 11 46 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 138 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 138 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 138 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 138 183 3 10 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 138 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 138 183
  (Polychromatic418967fa.accept_12_4_6_3_1_332 28 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 138 183 3 9 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 138 183 (Polychromatic418967fa.accept_10_6_8_3_1_930 26 138 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 138 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 138 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 138 183 3 8 46 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 138 183
  (Polychromatic418967fa.accept_11_1_6_7_1_116 23 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 138 183 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 138 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 138 183 3 7 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 138 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 20
  138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 138 183
  (Polychromatic418967fa.accept_13_6_8_1_1_2913 19 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 183 3 6 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 138 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 138 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 138 183 (Polychromatic418967fa.accept_10_6_8_3_1_930 16 138
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 138 183 3 5 46 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 138 183
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 138 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 138 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 138 183 3 4 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 138 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 11
  138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 138 183
  (Polychromatic418967fa.accept_7_3_5_1_1_72 10 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 138 183 3 3 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 138 183 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 138 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 138 183 (Polychromatic418967fa.accept_13_7_8_1_1_2145 7 138 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138 183 3 2 46 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 138 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 138 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 138 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 138 183 3 1 46 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 138 183 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 138 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 138 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 138 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 138 183)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 137 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 46 137 183 (accept_3_4 46 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 137 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 137 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 137 183 (accept_3_4 43 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 137 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 137 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 137 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 137 183 (accept_3_4 40 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 137 183 (Polychromatic418967fa.accept_19_1_4_12_1_6275 39 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 137 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 137 183 (accept_3_4 37 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 137 183 (Polychromatic418967fa.accept_10_6_7_3_1_547 36 137 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 137 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 137 183 (accept_3_4 34 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 137 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 137 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 137 183 (accept_3_4 31 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 137 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 137 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 137 183
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 137 183 (accept_3_4 28 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 137 183 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 137 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 137 183 (accept_3_4 25 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 137 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 137 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 137 183 (accept_3_4 22 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 137 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 137 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 137 183 (accept_3_4 19 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 137 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 137 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 137 183 (accept_3_4 16 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 137 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 137 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 137 183 (accept_3_4 13 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 137 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 183
  (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 137 183 (accept_3_4 10 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  137 183 (Polychromatic418967fa.accept_11_9_5_7_1_815 9 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 137 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 137 183 (accept_3_4 7 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 137 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 137 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 137 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 137 183 (accept_3_4 4 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  137 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 137 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 137 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 137 183 (accept_3_4 1 137 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 137 183))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 136 183 (Eq.refl
  Bool.true) (allA_succ_of_accept 47 136 183 (accept_3_5 47 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 136 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 46 136 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 136 183 (Polychromatic418967fa.accept_19_7_3_12_1_4787 45 136
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 136 183 (accept_3_5 44 136
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 136 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 136 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 42 136 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 136 183 (accept_3_5 41 136 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 136 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 136 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 39
  136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 136 183 (accept_3_5 38
  136 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 136 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 37 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 136 183 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 136 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 136 183 (accept_3_5 35 136 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 136 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 136 183 (Polychromatic418967fa.accept_7_5_3_1_1_424
  33 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 136 183 (accept_3_5 32
  136 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 136 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 136 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 136 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 136 183 (accept_3_5 29 136 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 136 183 (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 136 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 136 183
  (Polychromatic418967fa.accept_10_7_6_3_1_927 27 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 136 183 (accept_3_5 26 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 136 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 136 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 24 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 136 183 (accept_3_5 23 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 136 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 136 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 136 183
  (Polychromatic418967fa.accept_13_8_6_1_1_3808 21 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 136 183 (accept_3_5 20 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 136 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 136 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 136 183 (accept_3_5 17 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 136 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 136 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 136 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 15 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 136 183 (accept_3_5 14 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 136 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 136 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 136 183 (accept_3_5 11 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 136 183 (Polychromatic418967fa.accept_19_10_3_12_1_10566 10 136 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 136 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 136 183 (accept_3_5 8 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  136 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 136 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 136 183 (accept_3_5 5 136 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 136 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 136 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 136 183
  (Polychromatic418967fa.accept_11_3_4_7_1_114 3 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 136 183 (accept_3_5 2 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  136 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 136 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 136 183)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 135 183 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 135 183 3 16 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 135 183 (Polychromatic418967fa.accept_10_7_5_3_1_542 47 135 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 183
  (Polychromatic418967fa.accept_17_12_16_13_1_7951 46 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 45 135 183 3 15 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 44 135 183 (Polychromatic418967fa.accept_18_8_9_3_1_2645 44 135 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 183
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 43 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 135 183 3 14 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 135 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 135 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 183
  (Polychromatic418967fa.accept_21_19_9_15_1_4217 40 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 39 135 183 3 13 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 38 135 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 135 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 183
  (Polychromatic418967fa.accept_10_7_5_3_1_542 37 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 135 183 3 12 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 135 183 (Polychromatic418967fa.accept_13_9_5_1_1_1382 35 135 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 183
  (Polychromatic418967fa.accept_7_6_2_1_1_214 34 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 135 183 3 11 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 135 183 (Polychromatic418967fa.accept_10_2_5_3_1_1408 32 135 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 135 183 3 10 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 135 183 (Polychromatic418967fa.accept_13_3_5_1_1_2144 29 135 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 183
  (Polychromatic418967fa.accept_10_8_5_3_1_543 28 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 135 183 3 9 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 135 183 (Polychromatic418967fa.accept_11_4_3_7_1_828 26 135 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 183 (Polychromatic418967fa.accept_13_12_5_1_1_1383 25 135
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 135 183 3 8 45 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 135 183
  (Polychromatic418967fa.accept_19_4_2_12_1_10527 23 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 135 183 (Polychromatic418967fa.accept_10_2_5_3_1_1408 22 135 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 135 183 3 7 45 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 135 183
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 183 (Polychromatic418967fa.accept_13_6_5_1_1_834 19 135 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 135 183 3 6 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 135 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 17
  135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 183
  (Polychromatic418967fa.accept_13_3_5_1_1_2144 16 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 135 183 3 5 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 135 183 (Polychromatic418967fa.accept_18_14_9_3_1_6421 14 135 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 135 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 135 183 3 4 45 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 135 183
  (Polychromatic418967fa.accept_21_11_9_15_1_5746 11 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 135 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 135 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 135 183 3 3 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 135 183 (Polychromatic418967fa.accept_10_8_5_3_1_543 8
  135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 183
  (Polychromatic418967fa.accept_10_7_5_3_1_542 7 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 135 183 3 2 45 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 135 183 (Polychromatic418967fa.accept_20_5_15_3_1_4516 5 135 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 183 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 135 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 135 183 3 1 45 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 135 183
  (Polychromatic418967fa.accept_10_2_5_3_1_1408 2 135 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 183 (Polychromatic418967fa.accept_18_1_9_3_1_2672 1 135 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135 183))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 50 134
  183 (Eq.refl Bool.true) (allA_succ_of_accept 49 134 183 (accept_3_4 49 134 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 134 183 (Polychromatic418967fa.accept_18_12_8_3_1_1627 48 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 134 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 47 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 134 183 (accept_3_4 46 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 134 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 134 183 (Polychromatic418967fa.accept_13_5_4_1_1_364 44 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 134 183 (accept_3_4 43 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 134 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 134 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 134 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 41 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 134 183 (accept_3_4 40 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 134 183 (Polychromatic418967fa.accept_10_9_4_3_1_539 39 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 134 183 (Polychromatic418967fa.accept_9_2_8_3_1_181 38 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 134 183 (accept_3_4 37 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 134 183 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 134 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 134 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 134 183 (accept_3_4 34 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 134 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 134 183 (Polychromatic418967fa.accept_9_5_8_3_1_437 32 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 134 183 (accept_3_4 31 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 134 183 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 134 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 29 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 134 183 (accept_3_4 28 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 134 183 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 134 183 (Polychromatic418967fa.accept_15_11_14_3_1_1965 26 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 134 183 (accept_3_4 25 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 134 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 134 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 134 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 134 183 (accept_3_4 22 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 134 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 134 183 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 134 183 (accept_3_4 19 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 134 183 (Polychromatic418967fa.accept_12_6_2_3_1_354 18 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 134 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 134 183 (accept_3_4 16 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 134 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 134 183 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 134 183 (accept_3_4 13 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 134 183 (Polychromatic418967fa.accept_18_12_8_3_1_1627 12 134 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 134 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 134 183 (accept_3_4 10 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  134 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 134 183 (Polychromatic418967fa.accept_17_8_15_13_1_7942 8 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 134 183 (accept_3_4 7 134 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 134 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 134 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 134 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 134 183 (accept_3_4 4 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  134 183 (Polychromatic418967fa.accept_13_3_4_1_1_363 3 134 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 134 183 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 134 183 (accept_3_4 1 134 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 134 183)))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 51 133 183
  (Eq.refl Bool.true) (allA_succ_of_accept 50 133 183 (accept_3_5 50 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 133 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 133 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 133 183 (Polychromatic418967fa.accept_14_6_7_1_1_78 48 133 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 133 183 (accept_3_5 47 133 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 133 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 133 183
  (Polychromatic418967fa.accept_12_9_1_3_1_350 45 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 133 183 (accept_3_5 44 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 133 183 (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 133 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 133 183 (accept_3_5 41 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 133 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 133 183
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 39 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 133 183 (accept_3_5 38 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 133 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 133 183 (Polychromatic418967fa.accept_14_8_7_1_1_1615 36 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 133 183 (accept_3_5 35 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 133 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 133 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 133 183
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 133 183 (accept_3_5 32 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 133 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 133 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 133 183 (accept_3_5 29 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 133 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 133 183
  (Polychromatic418967fa.accept_14_13_7_1_1_1618 27 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 133 183 (accept_3_5 26 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 133 183 (Polychromatic418967fa.accept_15_10_13_3_1_4816 25 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 133 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 133 183 (accept_3_5 23 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 133 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 133 183
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 133 183 (accept_3_5 20 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 133 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 19 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 133 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 133 183 (accept_3_5 17 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 133 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 133 183
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 133 183 (accept_3_5 14 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 133 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 133 183 (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 133 183 (accept_3_5 11 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 133 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 133 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 133 183
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 133 183 (accept_3_5 8 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  133 183 (Polychromatic418967fa.accept_13_7_3_1_1_814 7 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 133 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 133 183 (accept_3_5 5 133 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 133 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 133 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 133 183
  (Polychromatic418967fa.accept_21_3_7_15_1_4300 3 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 133 183 (accept_3_5 2 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  133 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 133 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 133 183))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 52 132 183 (Eq.refl
  Bool.true) (allA_succ_of_gcd 51 132 183 3 17 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 50 132 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 50 132 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 132 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 183 3 16 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 132 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 132 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 132 183 3 15 44 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 132 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 132 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 132 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 132 183 3 14 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 132 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 132 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 40 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 132 183 3 13 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 132 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 38 132 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 132 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 37
  132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 132 183 3 12 44 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 132 183
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 132 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 132 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 132 183 3 11 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 132 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 132 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 183 3 10 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 132 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 132 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 132 183 3 9 44 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 132 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 132 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 132 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 183 3 8 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 23
  132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 132 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 132 183 3 7 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 132 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 132 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 132 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 132 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 132 183 3 6 44 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 132 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 132 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 132 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 132 183 3 5 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 132 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 132 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 183 3 4 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 11 132 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 132 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 132 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 132 183 3 3 44 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 132 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 132 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 132 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132 183 3 2 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 132 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 132 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 132 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 132 183 3 1 44 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 132 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 132 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 132 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 132 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  183)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 131 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 52 131 183 (accept_3_4 52 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 183 (accept_3_4 49 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 131 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 183 (accept_3_4 46 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 183 (accept_3_4 43 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 131 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 183 (accept_3_4 40 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 183 (accept_3_4 37 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 131 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 183
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 183 (accept_3_4 34 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 183 (accept_3_4 31 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 183 (Polychromatic418967fa.accept_20_10_11_3_1_1977 30 131 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 183 (accept_3_4 28 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 183 (accept_3_4 25 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 183
  (Polychromatic418967fa.accept_15_8_11_3_1_3847 23 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 183 (accept_3_4 22 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 183 (accept_3_4 19 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 131 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 183
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 183 (accept_3_4 16 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 183 (accept_3_4 13 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 131 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 183 (accept_3_4 10 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 183 (accept_3_4 7 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 183
  (Polychromatic418967fa.accept_19_5_17_12_1_6120 5 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 183 (accept_3_4 4 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 131 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 183 (accept_3_4 1 131 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131 183))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 54 130 183
  (Eq.refl Bool.true) (allA_succ_of_accept 53 130 183 (accept_3_5 53 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 130 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 130 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 130 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 130 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 130 183 (accept_3_5 50 130 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 49
  130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 130 183
  (Polychromatic418967fa.accept_21_6_4_15_1_9005 48 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 130 183 (accept_3_5 47 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 130 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 130 183 (accept_3_5 44 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 130 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 130 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 130 183 (accept_3_5 41 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 130 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 40 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 130 183 (Polychromatic418967fa.accept_14_11_4_1_1_4255 39 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 130 183 (accept_3_5 38 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 130 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 130 183
  (Polychromatic418967fa.accept_15_6_10_3_1_2844 36 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 130 183 (accept_3_5 35 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 130 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 130 183 (accept_3_5 32 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 130 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 130 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 130 183 (accept_3_5 29 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 130 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 28 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 130 183 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 130 183 (accept_3_5 26 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 130 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 130 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 130 183 (accept_3_5 23 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 130 183 (Polychromatic418967fa.accept_15_7_10_3_1_2891 22 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 130 183 (accept_3_5 20 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 130 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 130 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 130 183 (accept_3_5 17 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 130 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 130 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 130 183 (accept_3_5 14 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 130 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 130 183 (accept_3_5 11 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 130 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 130 183 (accept_3_5 8 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 130 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 130 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 6 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 130 183 (accept_3_5 5 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  130 183 (Polychromatic418967fa.accept_19_4_16_12_1_485 4 130 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 130 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 130 183 (accept_3_5 2 130 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 130 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 130 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 130
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 129 183 (Eq.refl Bool.true) (allA_succ_of_gcd
  54 129 183 3 18 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 129 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 183 (Polychromatic418967fa.accept_20_12_9_3_1_5999 52 129
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 129 183 3 17 43 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 129 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 50 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 49 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 129 183 3 16 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 129 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 47
  129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 129 183 3 15 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 129 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 129 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 183 (Polychromatic418967fa.accept_12_7_9_3_1_767
  43 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 129 183 3 14 43 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 129 183
  (Polychromatic418967fa.accept_12_5_9_3_1_85 41 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 129 183 3 13 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 129 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 38
  129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 37 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 129 183 3 12 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 129 183 (Polychromatic418967fa.accept_12_11_9_3_1_792 35 129 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 129 183 3 11 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 129 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 129 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 183 (Polychromatic418967fa.accept_12_7_9_3_1_767
  31 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 129 183 3 10 43 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 129 183
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 183 (Polychromatic418967fa.accept_13_2_12_1_1_343 28 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 129 183 3 9 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 129 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 26
  129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 129 183 3 8 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 129 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 129 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 129 183 3 7 43 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 129 183
  (Polychromatic418967fa.accept_15_5_9_3_1_528 20 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 129 183 3 6 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 129 183 (Polychromatic418967fa.accept_12_5_9_3_1_85 17
  129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 129 183 3 5 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 129 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 13 129
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 129 183 3 4 43 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 129 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 129 183 3 3 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 129 183 (Polychromatic418967fa.accept_13_8_12_1_1_4662 8 129 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 183
  (Polychromatic418967fa.accept_12_7_9_3_1_767 7 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 129 183 3 2 43 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 129 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 129 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 129 183 3 1 43 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 129 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 2 129 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 129 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 129 183))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  56 128 183 (Eq.refl Bool.true) (allA_succ_of_accept 55 128 183 (accept_3_4 55 128 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 128 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 54 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 128 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 53
  128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 128 183 (accept_3_4 52
  128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 128 183
  (Polychromatic418967fa.accept_9_6_2_3_1_771 51 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 128 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 50 128 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 128 183 (accept_3_4 49 128 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 128 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 128 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 47
  128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 128 183 (accept_3_4 46
  128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 128 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 128 183 (Polychromatic418967fa.accept_9_8_2_3_1_447 44 128 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 128 183 (accept_3_4 43 128 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 128 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 128 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 41
  128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 128 183 (accept_3_4 40
  128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 128 183
  (Polychromatic418967fa.accept_15_9_8_3_1_557 39 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 128 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 128 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 128 183 (accept_3_4 37 128 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 128 183 (Polychromatic418967fa.accept_10_6_8_3_1_930 36 128 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 128 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 128 183 (accept_3_4 34 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 128 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 128 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 32 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 128 183 (accept_3_4 31 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 128 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 128 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 128 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 128 183 (accept_3_4 28 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 128 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 128 183 (Polychromatic418967fa.accept_9_8_2_3_1_447 26 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 128 183 (accept_3_4 25 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 128 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 128 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 128 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 128 183 (accept_3_4 22 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 128 183 (Polychromatic418967fa.accept_10_1_8_3_1_947 21 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 128 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 128 183 (accept_3_4 19 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 128 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 128 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 128 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 128 183 (accept_3_4 16 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 128 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 128 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 14 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 128 183 (accept_3_4 13 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 128 183 (Polychromatic418967fa.accept_13_12_11_1_1_2920 12 128 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 128 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 128 183 (accept_3_4 10 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  128 183 (Polychromatic418967fa.accept_13_9_11_1_1_1375 9 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 128 183 (Polychromatic418967fa.accept_9_8_2_3_1_447 8 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 128 183 (accept_3_4 7 128 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 128 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 128 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 128 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 128 183 (accept_3_4 4 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  128 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 128 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 128 183 (Polychromatic418967fa.accept_19_2_14_12_1_7762 2 128 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 128 183 (accept_3_4 1 128 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 128 183)))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  57 127 183 (Eq.refl Bool.true) (allA_succ_of_accept 56 127 183 (accept_3_5 56 127 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 127 183 (Polychromatic418967fa.accept_10_5_7_3_1_561 55 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 127 183
  (Polychromatic418967fa.accept_10_4_7_3_1_54 54 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 127 183 (accept_3_5 53 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 127 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 127 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 127 183 (accept_3_5 50 127 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 127 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 127 183
  (Polychromatic418967fa.accept_13_9_10_1_1_1389 48 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 127 183 (accept_3_5 47 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 127 183 (Polychromatic418967fa.accept_10_5_7_3_1_561 45 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 127 183 (accept_3_5 44 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 127 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 127 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 127 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 127 183 (accept_3_5 41 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 127 183 (Polychromatic418967fa.accept_17_5_8_13_1_7994 39 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 127 183 (accept_3_5 38 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 127 183 (Polychromatic418967fa.accept_13_11_10_1_1_1409 37 127
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 127 183
  (Polychromatic418967fa.accept_10_6_7_3_1_547 36 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 127 183 (accept_3_5 35 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 127 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 127 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 127 183 (accept_3_5 32 127 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 127 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 31 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 127 183
  (Polychromatic418967fa.accept_13_4_10_1_1_1390 30 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 127 183 (accept_3_5 29 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 127 183 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 127 183 (accept_3_5 26 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 127 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 127 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 127 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 127 183 (accept_3_5 23 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 127 183 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 127 183 (accept_3_5 20 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 127 183 (Polychromatic418967fa.accept_15_4_7_3_1_119 19 127
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 127 183
  (Polychromatic418967fa.accept_19_18_13_12_1_4775 18 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 127 183 (accept_3_5 17 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 127 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 127 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 127 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 127 183 (accept_3_5 14 127 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 127 183 (Polychromatic418967fa.accept_9_4_1_3_1_190
  13 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 127 183
  (Polychromatic418967fa.accept_11_1_6_7_1_116 12 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 127 183 (accept_3_5 11 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 127 183 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 127 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 127 183 (accept_3_5 8 127 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 127 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 127 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 127 183 (accept_3_5 5 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  127 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 127 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 127 183 (Polychromatic418967fa.accept_16_3_15_7_1_3417 3 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 127 183 (accept_3_5 2 127 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 127 183 (Polychromatic418967fa.accept_11_1_6_7_1_116 1 127 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 127
  183))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 58 126 183 (Eq.refl Bool.true)
  (allA_succ_of_gcd 57 126 183 3 19 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 126 183 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 126 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 126 183
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 55 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 183 3 18 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 126 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 126 183 (Polychromatic418967fa.accept_12_4_6_3_1_332
  52 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 126 183 3 17 42 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 126 183
  (Polychromatic418967fa.accept_12_2_6_3_1_331 50 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 126 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 126 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 126 183 3 16 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 126 183 (Polychromatic418967fa.accept_10_7_6_3_1_927
  47 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 126 183
  (Polychromatic418967fa.accept_12_10_6_3_1_786 46 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 126 183 3 15 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 126 183 (Polychromatic418967fa.accept_12_8_6_3_1_366 44 126 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 126 183
  (Polychromatic418967fa.accept_23_20_11_22_1_10565 43 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 126 183 3 14 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 126 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 126 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 126 183
  (Polychromatic418967fa.accept_12_4_6_3_1_332 40 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 126 183 3 13 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 126 183 (Polychromatic418967fa.accept_10_8_6_3_1_1394 38 126 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 126 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 37 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 183 3 12 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 183 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 126 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 126 183 (Polychromatic418967fa.accept_12_10_6_3_1_786
  34 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 126 183 3 11 42 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 126 183
  (Polychromatic418967fa.accept_12_8_6_3_1_366 32 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 126 183 (Polychromatic418967fa.accept_11_9_5_7_1_815 31 126 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 126 183 3 10 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 126 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 29
  126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 126 183
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 28 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 126 183 3 9 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 126 183 (Polychromatic418967fa.accept_12_2_6_3_1_331 26 126 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 126 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 126 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 126 183 3 8 42 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 126 183
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 126 183 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 126 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 126 183 3 7 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 126 183 (Polychromatic418967fa.accept_11_9_5_7_1_815
  20 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 126 183
  (Polychromatic418967fa.accept_10_9_6_3_1_545 19 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 183 3 6 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 126 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 126 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 126 183 (Polychromatic418967fa.accept_12_4_6_3_1_332 16 126
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 126 183 3 5 42 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 126 183
  (Polychromatic418967fa.accept_12_2_6_3_1_331 14 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 126 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 126 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 126 183 3 4 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 126 183 (Polychromatic418967fa.accept_13_11_9_1_1_1407
  11 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 126 183
  (Polychromatic418967fa.accept_12_10_6_3_1_786 10 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 126 183 3 3 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 126 183 (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 126 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 126 183 (Polychromatic418967fa.accept_10_7_6_3_1_927 7 126 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126 183 3 2 42 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 126 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 5 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 126 183 (Polychromatic418967fa.accept_12_4_6_3_1_332 4 126 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 126 183 3 1 42 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 126 183 (Polychromatic418967fa.accept_12_2_6_3_1_331 2 126 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 126 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 1 126 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 126 183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 125 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 58 125 183 (accept_3_4 58 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 125 183 (Polychromatic418967fa.accept_10_7_5_3_1_542 57 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 125 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 125 183 (accept_3_4 55 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 125 183
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 53 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 125 183 (accept_3_4 52 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 125 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 125 183 (accept_3_4 49 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 125 183 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 125 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 47 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 125 183 (accept_3_4 46 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 125 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 125 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 125 183 (accept_3_4 43 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 125 183
  (Polychromatic418967fa.accept_9_5_8_3_1_437 41 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 125 183 (accept_3_4 40 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 125 183 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 125 183 (accept_3_4 37 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 125 183 (Polychromatic418967fa.accept_11_3_4_7_1_114 36 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 125 183
  (Polychromatic418967fa.accept_13_9_8_1_1_824 35 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 125 183 (accept_3_4 34 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 125 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 125 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 125 183 (accept_3_4 31 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 125 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 125 183 (accept_3_4 28 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 125 183 (Polychromatic418967fa.accept_10_7_5_3_1_542 27 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 125 183 (accept_3_4 25 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 125 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 125 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 125 183 (accept_3_4 22 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 125 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 125 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 125 183 (accept_3_4 19 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 125 183
  (Polychromatic418967fa.accept_10_7_5_3_1_542 17 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 125 183 (accept_3_4 16 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 125 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 125 183 (accept_3_4 13 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 125 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 125 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 125 183 (accept_3_4 10 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  125 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 125 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 125 183 (accept_3_4 7 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 125 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 125 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 125 183 (accept_3_4 4 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  125 183 (Polychromatic418967fa.accept_11_3_4_7_1_114 3 125 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 125 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 125 183 (accept_3_4 1 125 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 125 183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 60 124
  183 (Eq.refl Bool.true) (allA_succ_of_accept 59 124 183 (accept_3_5 59 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 124 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 124 183 (Polychromatic418967fa.accept_10_7_4_3_1_560
  57 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 124 183 (accept_3_5 56
  124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 124 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 55 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 124 183 (Polychromatic418967fa.accept_11_10_3_7_1_2564 54 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 124 183 (accept_3_5 53 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 52 124 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 124 183 (Polychromatic418967fa.accept_8_3_4_7_1_475
  51 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 124 183 (accept_3_5 50
  124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 124 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 49 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 124 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 124 183 (accept_3_5 47 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 46 124 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 46 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 124 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 45
  124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 124 183 (accept_3_5 44
  124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 124 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 43 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 124 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 124 183 (accept_3_5 41 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 124 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 124 183 (Polychromatic418967fa.accept_7_4_5_1_1_418
  39 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 124 183 (accept_3_5 38
  124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 124 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 37 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 124 183 (Polychromatic418967fa.accept_16_4_12_7_1_4475 36 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 124 183 (accept_3_5 35 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 124 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 34 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 124 183 (Polychromatic418967fa.accept_9_6_7_3_1_436
  33 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 124 183 (accept_3_5 32
  124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 124 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 31 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 124 183 (Polychromatic418967fa.accept_12_6_4_3_1_361 30 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 124 183 (accept_3_5 29 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 124 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 124 183 (Polychromatic418967fa.accept_7_6_5_1_1_416
  27 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 124 183 (accept_3_5 26
  124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 124 183
  (Polychromatic418967fa.accept_6_1_4_3_1_14 25 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 124 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 124 183 (accept_3_5 23 124 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 124 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 124 183
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 124 183 (accept_3_5 20 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 124 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 124 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 124 183 (accept_3_5 17 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 124 183 (Polychromatic418967fa.accept_13_3_7_1_1_334 16 124 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 124 183
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 124 183 (accept_3_5 14 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 124 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 124 183 (Polychromatic418967fa.accept_21_12_19_15_1_8942 12 124 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 124 183 (accept_3_5 11 124 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 124 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 124 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 124 183
  (Polychromatic418967fa.accept_10_9_4_3_1_539 9 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 124 183 (accept_3_5 8 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  124 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 124 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 124 183 (accept_3_5 5 124 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 124 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 124 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 124 183
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 124 183 (accept_3_5 2 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  124 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 124 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 124 183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 123 183
  (Eq.refl Bool.true) (allA_succ_of_gcd 60 123 183 3 20 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 123 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 123 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 123 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 123 183 3 19 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 123 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 123 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  55 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 123 183 3 18 41 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 123 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 123 183 3 17 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 123 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 50
  123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 123 183 3 16 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 123 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 123 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 123 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 123 183 3 15 41 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 123 183
  (Polychromatic418967fa.accept_8_4_3_7_1_491 44 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 123 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 123 183 3 14 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 123 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 123 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 40 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 123 183 3 13 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 123 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 123 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  37 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 123 183 3 12 41 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 123 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 34 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 123 183 3 11 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 123 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 123 183 3 10 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 123 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 123 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 123 183 (Polychromatic418967fa.accept_8_4_3_7_1_491
  28 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 123 183 3 9 41 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 123 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 123 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 123 183 3 8 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 123 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 123 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 123 183 3 7 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 123 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 20 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 123 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 123 183 3 6 41 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 123 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 123 183 3 5 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 123 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 123 183 3 4 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 123 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 123 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 123 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 123 183 3 3 41 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 123 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 123 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 123 183 3 2 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 123 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 123 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 123 183
  (Polychromatic418967fa.accept_8_4_3_7_1_491 4 123 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 123 183 3 1 41 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 123 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 123 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 123 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 123
  183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 122 183 (Eq.refl Bool.true)
  (allA_succ_of_gcd 61 122 183 61 1 2 3 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 60 122 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 122 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 122 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 122 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 122 183 (accept_3_4 58 122 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 57
  122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 122 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 122 183 (accept_3_4 55 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 122 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 122 183 (accept_3_4 52 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 122 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 122 183
  (Polychromatic418967fa.accept_11_6_1_7_1_1315 50 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 122 183 (accept_3_4 49 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 122 183 (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 122 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 122 183 (accept_3_4 46 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 122 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 122 183 (accept_3_4 43 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 122 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 122 183 (accept_3_4 40 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 122 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 122 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 122 183 (accept_3_4 37 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 122 183 (Polychromatic418967fa.accept_25_11_22_8_1_10564 36 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 122 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 122 183 (accept_3_4 34 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 122 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 122 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 122 183 (accept_3_4 31 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 122 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 122 183 (accept_3_4 28 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 122 183 (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 122 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 122 183
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 122 183 (accept_3_4 25 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 122 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 122 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 122 183 (accept_3_4 22 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 122 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 122 183 (accept_3_4 19 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 122 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 122 183 (accept_3_4 16 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 122 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 122 183
  (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 122 183 (accept_3_4 13 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 122 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 122 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 122 183 (accept_3_4 10 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 122 183
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 122 183 (accept_3_4 7 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  122 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 122 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 122 183 (accept_3_4 4 122 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 122 183 (Polychromatic418967fa.accept_13_3_5_1_1_2144 3 122 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 122 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 122 183 (accept_3_4 1 122 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 122
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 63 121 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 62 121 183 (accept_3_5 62 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 121 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 121 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 121 183 (accept_3_5 59 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 58 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 121 183
  (Polychromatic418967fa.accept_12_9_1_3_1_350 57 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 121 183 (accept_3_5 56 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 121 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 55 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 121 183 (accept_3_5 53 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 121 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 121 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 121 183 (accept_3_5 50 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 121 183 (Polychromatic418967fa.accept_13_10_4_1_1_2142 49 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 121 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 121 183 (accept_3_5 47 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 46 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 121 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 121 183 (accept_3_5 44 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 121 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 121 183 (accept_3_5 41 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 121 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 121 183
  (Polychromatic418967fa.accept_19_1_7_12_1_3443 39 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 121 183 (accept_3_5 38 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 121 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 121 183 (Polychromatic418967fa.accept_13_10_4_1_1_2142 36 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 121 183 (accept_3_5 35 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 121 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 121 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 33 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 121 183 (accept_3_5 32 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 121 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 121 183 (accept_3_5 29 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 121 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 121 183
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 121 183 (accept_3_5 26 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 121 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 121 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 121 183 (accept_3_5 23 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 121 183
  (Polychromatic418967fa.accept_12_9_1_3_1_350 21 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 121 183 (accept_3_5 20 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 121 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 121 183 (accept_3_5 17 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 121 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 121 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 15 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 121 183 (accept_3_5 14 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 121 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 121 183 (Polychromatic418967fa.accept_10_2_1_3_1_233 12 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 121 183 (accept_3_5 11 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 121 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 121 183
  (Polychromatic418967fa.accept_12_9_1_3_1_350 9 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 121 183 (accept_3_5 8 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  121 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 7 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 121 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 121 183 (accept_3_5 5 121 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 121 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 121 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 121 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 121 183 (accept_3_5 2 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  121 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 121 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 121 183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 120 183
  (Eq.refl Bool.true) (allA_succ_of_gcd 63 120 183 3 21 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 120 183 (Polychromatic418967fa.accept_18_8_12_3_1_2708 62 120
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 120 183
  (Polychromatic418967fa.accept_18_7_12_3_1_804 61 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 120 183 3 20 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 120 183 (Polychromatic418967fa.accept_13_7_3_1_1_814 59 120 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 120 183 (Polychromatic418967fa.accept_11_3_10_7_1_129
  58 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 120 183 3 19 40 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 120 183
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 56 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 120 183 (Polychromatic418967fa.accept_18_1_12_3_1_6426 55 120 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 120 183 3 18 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 120 183 (Polychromatic418967fa.accept_17_2_1_13_1_6670
  53 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 120 183
  (Polychromatic418967fa.accept_16_4_8_7_1_3396 52 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 120 183 3 17 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 120 183 (Polychromatic418967fa.accept_13_11_3_1_1_1397 50 120 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 120 183
  (Polychromatic418967fa.accept_14_7_8_1_1_1621 49 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 120 183 3 16 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 120 183 (Polychromatic418967fa.accept_11_3_10_7_1_129 47 120 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 120 183
  (Polychromatic418967fa.accept_13_7_3_1_1_814 46 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 120 183 3 15 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 120 183 (Polychromatic418967fa.accept_13_5_3_1_1_1398 44 120 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 120 183
  (Polychromatic418967fa.accept_13_4_3_1_1_2898 43 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 120 183 3 14 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 120 183 (Polychromatic418967fa.accept_13_2_3_1_1_3823 41 120 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 120 183
  (Polychromatic418967fa.accept_19_2_6_12_1_6270 40 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 120 183 3 13 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 120 183 (Polychromatic418967fa.accept_18_2_12_3_1_2707 38 120 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 120 183
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 37 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 120 183 3 12 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 120 183 (Polychromatic418967fa.accept_14_7_8_1_1_1621 35 120 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 120 183
  (Polychromatic418967fa.accept_19_15_6_12_1_7746 34 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 33 120 183 3 11 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 32 120 183 (Polychromatic418967fa.accept_13_6_3_1_1_1413 32 120 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 120 183
  (Polychromatic418967fa.accept_13_5_3_1_1_1398 31 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 120 183 3 10 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 120 183 (Polychromatic418967fa.accept_17_12_1_13_1_6672 29 120 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 120 183
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 28 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 120 183 3 9 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 120 183 (Polychromatic418967fa.accept_18_8_12_3_1_2708 26 120 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 120 183 (Polychromatic418967fa.accept_11_3_10_7_1_129 25 120
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 120 183 3 8 40 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 120 183
  (Polychromatic418967fa.accept_14_9_8_1_1_2381 23 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 120 183 (Polychromatic418967fa.accept_25_22_20_8_1_10563 22 120 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 120 183 3 7 40 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 120 183
  (Polychromatic418967fa.accept_13_7_3_1_1_814 20 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 120 183 (Polychromatic418967fa.accept_13_6_3_1_1_1413 19 120 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 120 183 3 6 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 120 183 (Polychromatic418967fa.accept_13_4_3_1_1_2898
  17 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 120 183
  (Polychromatic418967fa.accept_14_2_8_1_1_1647 16 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 120 183 3 5 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 120 183 (Polychromatic418967fa.accept_11_3_10_7_1_129 14 120 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 120 183 (Polychromatic418967fa.accept_18_13_12_3_1_3857 13 120
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 120 183 3 4 40 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 120 183
  (Polychromatic418967fa.accept_13_11_3_1_1_1397 11 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 120 183 (Polychromatic418967fa.accept_19_10_6_12_1_10562 10 120 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 120 183 3 3 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 120 183 (Polychromatic418967fa.accept_18_8_12_3_1_2708
  8 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 120 183
  (Polychromatic418967fa.accept_13_7_3_1_1_814 7 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 120 183 3 2 40 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 120 183 (Polychromatic418967fa.accept_13_5_3_1_1_1398 5 120 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 120 183 (Polychromatic418967fa.accept_13_4_3_1_1_2898 4 120 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 120 183 3 1 40 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 120 183
  (Polychromatic418967fa.accept_13_2_3_1_1_3823 2 120 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 120 183 (Polychromatic418967fa.accept_16_1_8_7_1_3377 1 120 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 120 183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 65 119 183 (Eq.refl Bool.true) (allA_succ_of_accept 64 119 183 (accept_3_4 64 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 119 183 (Polychromatic418967fa.accept_25_13_19_8_1_10561 63 119 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 62 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 119 183 (accept_3_4 61 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 119 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 60 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 119 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 59 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 119 183 (accept_3_4 58 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 119 183 (Polychromatic418967fa.accept_11_2_9_7_1_124 57 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 56 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 119 183 (accept_3_4 55 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 119 183 (Polychromatic418967fa.accept_10_4_9_3_1_1907 54 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 119 183 (Polychromatic418967fa.accept_9_8_2_3_1_447 53 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 119 183 (accept_3_4 52 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 119 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 50 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 119 183 (accept_3_4 49 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 119 183 (Polychromatic418967fa.accept_13_9_2_1_1_813 48 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 119 183 (Polychromatic418967fa.accept_15_2_14_3_1_1916 47 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 119 183 (accept_3_4 46 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 119 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 45 119
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 44 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 119 183 (accept_3_4 43 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 119 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 119 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 41 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 119 183 (accept_3_4 40 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 119 183 (Polychromatic418967fa.accept_19_1_5_12_1_6249 39 119 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 38 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 119 183 (accept_3_4 37 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 119 183 (Polychromatic418967fa.accept_10_6_9_3_1_935 36 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 119 183 (Polychromatic418967fa.accept_9_8_2_3_1_447 35 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 119 183 (accept_3_4 34 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 119 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 32 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 119 183 (accept_3_4 31 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 119 183 (Polychromatic418967fa.accept_19_11_5_12_1_3439 30 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 119 183 (Polychromatic418967fa.accept_13_3_2_1_1_2907 29 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 119 183 (accept_3_4 28 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 119 183 (Polychromatic418967fa.accept_11_5_9_7_1_411 27 119
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 26 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 119 183 (accept_3_4 25 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 119 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 119 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 23 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 119 183 (accept_3_4 22 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 119 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 20 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 119 183 (accept_3_4 19 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 119 183 (Polychromatic418967fa.accept_21_18_14_15_1_5809 18 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 17 119 183 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 119 183 (accept_3_4 16 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 119 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 119 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 14 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 119 183 (accept_3_4 13 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 119 183 (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 119 183 (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 119 183 (accept_3_4 10 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 119 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 119 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 8 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 119 183 (accept_3_4 7 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  119 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 119 183 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 119 183 (accept_3_4 4 119 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 119 183 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 119 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 119 183
  (Polychromatic418967fa.accept_6_2_5_3_1_16 2 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 119 183 (accept_3_4 1 119 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 119
  183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 66 118 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 65 118 183 (accept_3_5 65 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 118 183 (Polychromatic418967fa.accept_19_7_4_12_1_4769 64 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 118 183 (Polychromatic418967fa.accept_14_7_6_1_1_1656 63 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 118 183 (accept_3_5 62 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 118 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 118 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 60 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 118 183 (accept_3_5 59 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 118 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 58 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 118 183 (accept_3_5 56 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 118 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 118 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 54 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 118 183 (accept_3_5 53 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 118 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 52 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 118 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 118 183 (accept_3_5 50 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 118 183
  (Polychromatic418967fa.accept_11_4_8_7_1_819 48 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 118 183 (accept_3_5 47 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 118 183 (Polychromatic418967fa.accept_10_6_8_3_1_930 46 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 118 183 (accept_3_5 44 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 118 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 118 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 42 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 118 183 (accept_3_5 41 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 118 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 118 183 (Polychromatic418967fa.accept_15_9_13_3_1_535 39 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 118 183 (accept_3_5 38 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 118 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 118 183
  (Polychromatic418967fa.accept_10_6_8_3_1_930 36 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 118 183 (accept_3_5 35 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 118 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 34 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 118 183 (accept_3_5 32 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 118 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 118 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 118 183 (accept_3_5 29 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 118 183 (Polychromatic418967fa.accept_20_8_18_3_1_10560 28 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 118 183 (Polychromatic418967fa.accept_15_12_13_3_1_1915 27 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 118 183 (accept_3_5 26 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 118 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 118 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 118 183 (accept_3_5 23 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 118 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 118 183 (accept_3_5 20 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 118 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 118 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 18 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 118 183 (accept_3_5 17 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 118 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 118 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 118 183 (accept_3_5 14 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 118 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 12 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 118 183 (accept_3_5 11 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 118 183 (Polychromatic418967fa.accept_15_10_13_3_1_4816 10 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 118 183 (accept_3_5 8 118 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 118 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 118 183
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 118 183 (accept_3_5 5 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  118 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 118 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 118 183 (Polychromatic418967fa.accept_17_3_16_13_1_6635 3 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 118 183 (accept_3_5 2 118 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 118 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 118 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 118
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 117 183 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 117 183 3 22 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 117 183 (Polychromatic418967fa.accept_10_5_7_3_1_561 65 117 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 117 183 (Polychromatic418967fa.accept_10_4_7_3_1_54
  64 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 117 183 3 21 39 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 117 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 117 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 61 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 117 183 3 20 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 117 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 59
  117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 117 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 117 183 3 19 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 117 183 (Polychromatic418967fa.accept_10_6_7_3_1_547 56 117 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 117 183 (Polychromatic418967fa.accept_7_6_5_1_1_416
  55 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 117 183 3 18 39 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 117 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 53 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 117 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 52 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 117 183 3 17 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 117 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 117 183
  (Polychromatic418967fa.accept_12_1_9_3_1_370 49 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 117 183 3 16 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 117 183 (Polychromatic418967fa.accept_12_11_9_3_1_792 47 117 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 117 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 46 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 45 117 183 3 15 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 44 117 183 (Polychromatic418967fa.accept_10_4_7_3_1_54 44 117 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 117 183 (Polychromatic418967fa.accept_12_7_9_3_1_767
  43 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 117 183 3 14 39 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 117 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 41 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 117 183 (Polychromatic418967fa.accept_19_2_3_12_1_10559 40 117 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 117 183 3 13 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 117 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 38 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 117 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 37 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 117 183 3 12 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 117 183 (Polychromatic418967fa.accept_10_5_7_3_1_561
  35 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 117 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 34 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 117 183 3 11 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 117 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 117 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 117 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 31
  117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 117 183 3 10 39 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 117 183
  (Polychromatic418967fa.accept_12_5_9_3_1_85 29 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 117 183 (Polychromatic418967fa.accept_15_13_12_3_1_1180 28 117 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 117 183 3 9 39 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 117 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 117 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 117 183 3 8 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 117 183 (Polychromatic418967fa.accept_12_11_9_3_1_792
  23 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 117 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 117 183 3 7 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 117 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 117 183 (Polychromatic418967fa.accept_12_7_9_3_1_767 19 117
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 117 183 3 6 39 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 117 183
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 117 183 (Polychromatic418967fa.accept_10_6_7_3_1_547 16 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 117 183 3 5 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 117 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 117 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 117 183 3 4 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 117 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 117 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 117 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 117 183 3 3 39 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 117 183
  (Polychromatic418967fa.accept_15_8_12_3_1_1912 8 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 117 183 (Polychromatic418967fa.accept_12_7_9_3_1_767 7 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 117 183 3 2 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 117 183 (Polychromatic418967fa.accept_10_5_7_3_1_561 5 117 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 117 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 4 117 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 117 183 3 1 39 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 117 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 117 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 117 183 (Polychromatic418967fa.accept_12_1_9_3_1_370 1 117 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 117
  183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 116 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 67 116 183 (accept_3_4 67 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 116 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 116 183 (accept_3_4 64 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 116 183 (Polychromatic418967fa.accept_13_11_12_1_1_2154 63 116 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 116 183
  (Polychromatic418967fa.accept_16_14_4_7_1_2380 62 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 116 183 (accept_3_4 61 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 116 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 60 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 116 183 (accept_3_4 58 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 116 183 (Polychromatic418967fa.accept_10_7_6_3_1_927 57 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 116 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 56 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 116 183 (accept_3_4 55 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 116 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 116 183 (accept_3_4 52 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 116 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 51 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 116 183
  (Polychromatic418967fa.accept_9_5_8_3_1_437 50 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 116 183 (accept_3_4 49 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 116 183 (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 116 183 (accept_3_4 46 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 116 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 116 183
  (Polychromatic418967fa.accept_13_5_12_1_1_2123 44 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 116 183 (accept_3_4 43 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 116 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 41 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 116 183 (accept_3_4 40 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 116 183 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 116 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 116 183 (accept_3_4 37 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 116 183 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 116 183 (accept_3_4 34 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 116 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 116 183
  (Polychromatic418967fa.accept_9_5_8_3_1_437 32 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 116 183 (accept_3_4 31 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 116 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 30 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 29 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 116 183 (accept_3_4 28 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 116 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 27 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 116 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 116 183 (accept_3_4 25 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 116 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 116 183 (accept_3_4 22 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 116 183 (Polychromatic418967fa.accept_13_8_12_1_1_4662 21 116 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 116 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 20 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 116 183 (accept_3_4 19 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 116 183 (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 17 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 116 183 (accept_3_4 16 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 116 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 116 183
  (Polychromatic418967fa.accept_9_5_8_3_1_437 14 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 116 183 (accept_3_4 13 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 116 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 116 183 (accept_3_4 10 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 116 183 (Polychromatic418967fa.accept_10_9_6_3_1_545 9 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 116 183
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 8 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 116 183 (accept_3_4 7 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  116 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 116 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 5 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 116 183 (accept_3_4 4 116 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 116 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 116 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 116 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 2 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 116 183 (accept_3_4 1 116 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 116
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 69 115 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 68 115 183 (accept_3_5 68 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 115 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 67 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 115 183 (Polychromatic418967fa.accept_15_6_10_3_1_2844 66 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 115 183 (accept_3_5 65 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 115 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 115 183
  (Polychromatic418967fa.accept_16_15_3_7_1_3389 63 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 115 183 (accept_3_5 62 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 115 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 61 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 115 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 115 183 (accept_3_5 59 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 115 183
  (Polychromatic418967fa.accept_10_7_5_3_1_542 57 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 115 183 (accept_3_5 56 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 115 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 55 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 115 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 115 183 (accept_3_5 53 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 52 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 115 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 115 183 (accept_3_5 50 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 115 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 49 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 115 183 (Polychromatic418967fa.accept_10_8_5_3_1_543 48 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 115 183 (accept_3_5 47 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 115 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 115 183
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 45 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 115 183 (accept_3_5 44 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 115 183 (Polychromatic418967fa.accept_15_13_10_3_1_1952 43 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 115 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 42 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 115 183 (accept_3_5 41 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 115 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 115 183 (accept_3_5 38 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 115 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 115 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 115 183 (accept_3_5 35 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 115 183
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 115 183 (accept_3_5 32 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 115 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 115 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 115 183 (accept_3_5 29 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 28 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 115 183
  (Polychromatic418967fa.accept_10_7_5_3_1_542 27 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 115 183 (accept_3_5 26 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 115 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 115 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 115 183 (accept_3_5 23 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 115 183
  (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 115 183 (accept_3_5 20 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 115 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 115 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 115 183 (accept_3_5 17 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 16 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 115 183
  (Polychromatic418967fa.accept_9_6_7_3_1_436 15 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 115 183 (accept_3_5 14 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 115 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 115 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 115 183 (accept_3_5 11 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 10 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 115 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 115 183 (accept_3_5 8 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  115 183 (Polychromatic418967fa.accept_10_7_5_3_1_542 7 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 115 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 115 183 (accept_3_5 5 115 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 115 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 115 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 115 183
  (Polychromatic418967fa.accept_13_3_11_1_1_2122 3 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 115 183 (accept_3_5 2 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  115 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 115 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 115 183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 114
  183 (Eq.refl Bool.true) (allA_succ_of_gcd 69 114 183 3 23 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 114 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 68 114 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 114 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 114 183 3 22 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 114 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 114 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 114 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  64 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 114 183 3 21 38 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 114 183
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 114 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 114 183 3 20 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 114 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 59
  114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 114 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 58 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 114 183 3 19 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 114 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 114 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 114 183 (Polychromatic418967fa.accept_7_6_2_1_1_214
  55 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 114 183 3 18 38 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 114 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 114 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 52 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 114 183 3 17 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 114 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 50
  114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 114 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 114 183 3 16 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 114 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 114 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 114 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  46 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 114 183 3 15 38 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 114 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 114 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 114 183 3 14 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 114 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 114 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 114 183 3 13 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 114 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 114 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 114 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 114 183 3 12 38 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 114 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 114 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 114 183 3 11 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 114 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 114 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 31 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 114 183 3 10 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 114 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 114 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 114 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 114 183 3 9 38 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 114 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 114 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 114 183 3 8 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 114 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 114 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 114 183 3 7 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 114 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 114 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 114 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 114 183 3 6 38 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 114 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 17 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 114 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 114 183 3 5 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 114 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 114 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 13 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 114 183 3 4 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 114 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 114 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 114 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 114 183 3 3 38 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 114 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 114 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 114 183 3 2 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 114 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 114 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 114 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 114 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 114 183 3 1 38 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 114 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 114 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 114 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 114 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 114
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 113 183 (Eq.refl Bool.true)
  (allA_succ_of_accept 70 113 183 (accept_3_4 70 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 113 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 113 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 113 183 (accept_3_4 67 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 113 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 65 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 113 183 (accept_3_4 64 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 113 183 (Polychromatic418967fa.accept_13_11_9_1_1_1407 63 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 113 183 (accept_3_4 61 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 113 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 113 183
  (Polychromatic418967fa.accept_11_4_3_7_1_828 59 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 113 183 (accept_3_4 58 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 113 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 113 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 113 183 (accept_3_4 55 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 113 183
  (Polychromatic418967fa.accept_9_8_5_3_1_777 53 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 113 183 (accept_3_4 52 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 113 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 51 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 113 183 (accept_3_4 49 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 113 183 (Polychromatic418967fa.accept_11_4_3_7_1_828 48 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 113 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 47 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 113 183 (accept_3_4 46 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 113 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 113 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 113 183 (accept_3_4 43 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 113 183
  (Polychromatic418967fa.accept_13_2_9_1_1_67 41 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 113 183 (accept_3_4 40 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 113 183 (Polychromatic418967fa.accept_15_9_8_3_1_557 39 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 113 183 (accept_3_4 37 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 113 183 (Polychromatic418967fa.accept_13_10_9_1_1_5609 36 113 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 113 183
  (Polychromatic418967fa.accept_9_8_5_3_1_777 35 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 113 183 (accept_3_4 34 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 113 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 33 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 113 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 113 183 (accept_3_4 31 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 113 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 29 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 113 183 (accept_3_4 28 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 113 183 (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 113 183 (accept_3_4 25 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 113 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 113 183
  (Polychromatic418967fa.accept_13_10_9_1_1_5609 23 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 113 183 (accept_3_4 22 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 113 183 (Polychromatic418967fa.accept_11_10_3_7_1_2564 21 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 113 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 113 183 (accept_3_4 19 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 113 183
  (Polychromatic418967fa.accept_9_8_5_3_1_777 17 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 113 183 (accept_3_4 16 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 113 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 113 183 (accept_3_4 13 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 113 183 (Polychromatic418967fa.accept_15_12_8_3_1_1995 12 113 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 113 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 113 183 (accept_3_4 10 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  113 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 9 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 113 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 113 183 (accept_3_4 7 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 113 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 113 183
  (Polychromatic418967fa.accept_13_5_9_1_1_1405 5 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 113 183 (accept_3_4 4 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  113 183 (Polychromatic418967fa.accept_21_3_8_15_1_4301 3 113 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 113 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 113 183 (accept_3_4 1 113 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 113 183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 72 112 183 (Eq.refl Bool.true) (allA_succ_of_accept 71 112 183 (accept_3_5 71 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 70 112 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 70 112 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 112 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 69 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 68 112 183 (accept_3_5 68 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  67 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 66 112 183 (Polychromatic418967fa.accept_12_6_4_3_1_361 66 112 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 112 183 (accept_3_5 65 112 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 112 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 64 112 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 112 183
  (Polychromatic418967fa.accept_13_11_8_1_1_3815 63 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 112 183 (accept_3_5 62 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  61 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 61 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 112 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 60 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 112 183 (accept_3_5 59 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 58 112 183 (Polychromatic418967fa.accept_13_6_8_1_1_2913 58 112 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 112 183
  (Polychromatic418967fa.accept_13_5_8_1_1_2161 57 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 112 183 (accept_3_5 56 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  55 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 112 183 (Polychromatic418967fa.accept_12_6_4_3_1_361 54 112 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 112 183 (accept_3_5 53 112 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 112 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 52 112 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 112 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 51 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 112 183 (accept_3_5 50 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  49 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 49 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 112 183 (Polychromatic418967fa.accept_13_9_8_1_1_824 48 112 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 112 183 (accept_3_5 47 112 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 112 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 46 112 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 112 183
  (Polychromatic418967fa.accept_10_5_2_3_1_239 45 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 112 183 (accept_3_5 44 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  43 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 112 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 42 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 112 183 (accept_3_5 41 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 112 183 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 112 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 112 183
  (Polychromatic418967fa.accept_17_5_10_13_1_10558 39 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 112 183 (accept_3_5 38 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 37 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 112 183 (Polychromatic418967fa.accept_25_11_12_8_1_10557 36
  112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 112 183 (accept_3_5 35
  112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 112 183
  (Polychromatic418967fa.accept_9_7_4_3_1_204 34 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 112 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 112 183 (accept_3_5 32 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 112 183 (Polychromatic418967fa.accept_12_6_4_3_1_361
  30 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 112 183 (accept_3_5 29
  112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 112 183
  (Polychromatic418967fa.accept_9_1_4_3_1_201 28 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 112 183 (Polychromatic418967fa.accept_15_12_7_3_1_1940 27 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 112 183 (accept_3_5 26 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 25 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 112 183 (Polychromatic418967fa.accept_9_6_4_3_1_203
  24 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 112 183 (accept_3_5 23
  112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 112 183
  (Polychromatic418967fa.accept_13_9_8_1_1_824 22 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 112 183 (Polychromatic418967fa.accept_10_1_2_3_1_1910 21 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 112 183 (accept_3_5 20 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 112 183 (Polychromatic418967fa.accept_12_6_4_3_1_361
  18 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 112 183 (accept_3_5 17
  112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 112 183
  (Polychromatic418967fa.accept_9_7_4_3_1_204 16 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 15 112 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 112 183 (accept_3_5 14 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 13 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 112 183 (Polychromatic418967fa.accept_13_12_8_1_1_825
  12 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 112 183 (accept_3_5 11
  112 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 112 183
  (Polychromatic418967fa.accept_9_1_4_3_1_201 10 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 112 183 (Polychromatic418967fa.accept_11_9_2_7_1_1298 9 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 112 183 (accept_3_5 8 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 7 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 112 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 6
  112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 112 183 (accept_3_5 5 112
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 112 183
  (Polychromatic418967fa.accept_15_4_7_3_1_119 4 112 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 112 183 (Polychromatic418967fa.accept_17_3_10_13_1_2021 3 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 112 183 (accept_3_5 2 112 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 112 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 1 112 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 112
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 73 111 183 (Eq.refl Bool.true)
  (allA_succ_of_gcd 72 111 183 3 24 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 111 183 (Polychromatic418967fa.accept_13_6_7_1_1_335 71 111 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 111 183
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 70 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 111 183 3 23 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 111 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 68 111 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 111 183
  (Polychromatic418967fa.accept_16_3_15_7_1_3417 67 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 111 183 3 22 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 111 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 111 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 111 183
  (Polychromatic418967fa.accept_19_7_16_12_1_10556 64 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 63 111 183 3 21 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 62 111 183 (Polychromatic418967fa.accept_10_2_1_3_1_233 62 111 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 111 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 61 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 111 183 3 20 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 111 183 (Polychromatic418967fa.accept_16_11_15_7_1_5654 59 111 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 111 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 58 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 111 183 3 19 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 111 183 (Polychromatic418967fa.accept_15_11_6_3_1_1192 56 111 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 111 183
  (Polychromatic418967fa.accept_13_3_7_1_1_334 55 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 111 183 3 18 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 111 183 (Polychromatic418967fa.accept_19_15_16_12_1_4779 53 111 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 111 183
  (Polychromatic418967fa.accept_10_2_1_3_1_233 52 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 111 183 3 17 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 111 183 (Polychromatic418967fa.accept_11_6_1_7_1_1315 50 111 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 111 183
  (Polychromatic418967fa.accept_14_7_13_1_1_922 49 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 111 183 3 16 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 111 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 111 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 111 183 (Polychromatic418967fa.accept_15_1_6_3_1_2827
  46 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 111 183 3 15 37 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 111 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 111 183 (Polychromatic418967fa.accept_16_11_15_7_1_5654 43 111 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 111 183 3 14 37 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 111 183
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 111 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 40 111 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 111 183 3 13 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 111 183 (Polychromatic418967fa.accept_10_8_1_3_1_1374
  38 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 111 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 37 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 111 183 3 12 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 111 183 (Polychromatic418967fa.accept_14_7_13_1_1_922 35 111 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 111 183
  (Polychromatic418967fa.accept_13_8_7_1_1_1385 34 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 111 183 3 11 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 111 183 (Polychromatic418967fa.accept_10_2_1_3_1_233 32 111 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 111 183 (Polychromatic418967fa.accept_15_1_6_3_1_2827
  31 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 111 183 3 10 37 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 111 183
  (Polychromatic418967fa.accept_13_3_7_1_1_334 29 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 111 183 (Polychromatic418967fa.accept_10_8_1_3_1_1374 28 111 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 111 183 3 9 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 111 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 26
  111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 111 183
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 111 183 3 8 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 111 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 111 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 111 183 (Polychromatic418967fa.accept_10_2_1_3_1_233 22 111
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 111 183 3 7 37 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 111 183
  (Polychromatic418967fa.accept_15_5_6_3_1_525 20 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 111 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 111 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 111 183 3 6 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 111 183 (Polychromatic418967fa.accept_11_6_1_7_1_1315
  17 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 111 183
  (Polychromatic418967fa.accept_7_2_6_1_1_73 16 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 111 183 3 5 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 111 183 (Polychromatic418967fa.accept_16_14_15_7_1_5655 14 111 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 111 183
  (Polychromatic418967fa.accept_19_13_16_12_1_6096 13 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 111 183 3 4 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 111 183 (Polychromatic418967fa.accept_13_11_7_1_1_1386 11 111 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 111 183
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 10 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 111 183 3 3 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 111 183 (Polychromatic418967fa.accept_10_8_1_3_1_1374 8 111 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 111 183 (Polychromatic418967fa.accept_14_7_13_1_1_922 7 111 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 111 183 3 2 37 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 111 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 111 183 (Polychromatic418967fa.accept_17_4_9_13_1_2020 4 111 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 111 183 3 1 37 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 111 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 111 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 111 183
  (Polychromatic418967fa.accept_15_1_6_3_1_2827 1 111 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 111 183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 110 183
  (Eq.refl Bool.true) (allA_succ_of_accept 73 110 183 (accept_3_4 73 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 110 183 (Polychromatic418967fa.accept_13_7_6_1_1_368 72 110 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 110 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 110 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 110 183 (accept_3_4 70 110 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 69
  110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 110 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 68 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 110 183 (accept_3_4 67 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 110 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 110 183 (accept_3_4 64 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 110 183 (Polychromatic418967fa.accept_16_15_14_7_1_10555 63 110 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 110 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 110 183 (accept_3_4 61 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 110 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 110 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 110 183 (accept_3_4 58 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 110 183
  (Polychromatic418967fa.accept_17_5_8_13_1_7994 56 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 110 183 (accept_3_4 55 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 110 183 (Polychromatic418967fa.accept_12_6_2_3_1_354 54 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 53 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 110 183 (accept_3_4 52 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 110 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 51 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 110 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 50 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 110 183 (accept_3_4 49 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 110 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 110 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 47 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 110 183 (accept_3_4 46 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 110 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 44 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 110 183 (accept_3_4 43 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 110 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 42 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 41 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 110 183 (accept_3_4 40 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 110 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 110 183
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 110 183 (accept_3_4 37 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 110 183 (Polychromatic418967fa.accept_15_6_5_3_1_1988 36 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 110 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 35 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 110 183 (accept_3_4 34 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 110 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 110 183 (accept_3_4 31 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 110 183 (Polychromatic418967fa.accept_12_6_2_3_1_354 30 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 110 183 (accept_3_4 28 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 110 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 110 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 110 183 (accept_3_4 25 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 110 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 110 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 23 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 110 183 (accept_3_4 22 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 110 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 110 183 (accept_3_4 19 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 110 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 17 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 110 183 (accept_3_4 16 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 110 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 110 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 110 183 (accept_3_4 13 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 110 183 (Polychromatic418967fa.accept_18_12_2_3_1_6414 12 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 110 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 11 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 110 183 (accept_3_4 10 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 110 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 110 183 (accept_3_4 7 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  110 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 110 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 110 183 (accept_3_4 4 110 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 110 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 110 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 110 183
  (Polychromatic418967fa.accept_13_2_6_1_1_3807 2 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 110 183 (accept_3_4 1 110 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 110
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 75 109 183 (Eq.refl
  Bool.true) (allA_succ_of_accept 74 109 183 (accept_3_5 74 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 109 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 73 109 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 109 183 (Polychromatic418967fa.accept_20_12_9_3_1_5999 72 109
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 109 183 (accept_3_5 71 109
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 109 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 70 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 69 109 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 69 109 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 109 183 (accept_3_5 68 109 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 109 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 67 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 109 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 66
  109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 109 183 (accept_3_5 65
  109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 109 183
  (Polychromatic418967fa.accept_6_4_1_3_1_77 64 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 63 109 183 (Polychromatic418967fa.accept_18_9_1_3_1_6451 63 109 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 109 183 (accept_3_5 62 109 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 109 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 61 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 109 183 (Polychromatic418967fa.accept_9_6_1_3_1_191
  60 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 109 183 (accept_3_5 59
  109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 109 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 109 183 (Polychromatic418967fa.accept_12_9_1_3_1_350 57 109 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 109 183 (accept_3_5 56 109 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 109 183 (Polychromatic418967fa.accept_13_3_5_1_1_2144 55 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 109 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 54 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 109 183 (accept_3_5 53 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 109 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 109 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 51 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 109 183 (accept_3_5 50 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 109 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 49 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 109 183
  (Polychromatic418967fa.accept_13_9_5_1_1_1382 48 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 109 183 (accept_3_5 47 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 109 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 46 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 109 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 109 183 (accept_3_5 44 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 109 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 43 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 109 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 42 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 109 183 (accept_3_5 41 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 109 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 109 183 (Polychromatic418967fa.accept_20_19_9_3_1_10554 39 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 109 183 (accept_3_5 38 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 109 183 (Polychromatic418967fa.accept_15_7_4_3_1_1930 37 109
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 109 183
  (Polychromatic418967fa.accept_10_6_9_3_1_935 36 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 109 183 (accept_3_5 35 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 109 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 109 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 109 183 (accept_3_5 32 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 109 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 109 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 30 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 109 183 (accept_3_5 29 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 109 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 109 183 (Polychromatic418967fa.accept_18_9_1_3_1_6451 27 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 109 183 (accept_3_5 26 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 109 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 25 109 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 109 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 24 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 109 183 (accept_3_5 23 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 109 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 22 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 109 183 (Polychromatic418967fa.accept_12_9_1_3_1_350 21 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 109 183 (accept_3_5 20 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 109 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 109 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 109 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 18 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 109 183 (accept_3_5 17 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 109 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 109 183 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 109 183 (accept_3_5 14 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 109 183 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 109 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 12 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 109 183 (accept_3_5 11 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 109 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 109 183 (Polychromatic418967fa.accept_12_9_1_3_1_350 9 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 109 183 (accept_3_5 8 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 109 183 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 109 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 6 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 109 183 (accept_3_5 5 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  109 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 109 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 109 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 109 183 (accept_3_5 2 109 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 109 183 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1 109 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 109
  183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 108 183 (Eq.refl
  Bool.true) (allA_succ_of_gcd 75 108 183 3 25 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 74 108 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 74 108 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 108 183
  (Polychromatic418967fa.accept_19_16_13_12_1_7749 73 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 72 108 183 3 24 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 71 108 183 (Polychromatic418967fa.accept_10_1_8_3_1_947 71 108 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 108 183
  (Polychromatic418967fa.accept_13_5_4_1_1_364 70 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 69 108 183 3 23 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 68 108 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 68 108 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 108 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 67
  108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 108 183 3 22 36 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 108 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 108 183 (Polychromatic418967fa.accept_21_1_3_15_1_5797 64 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 108 183 3 21 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 108 183 (Polychromatic418967fa.accept_13_10_4_1_1_2142
  62 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 108 183
  (Polychromatic418967fa.accept_7_5_3_1_1_424 61 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 108 183 3 20 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 108 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 59 108 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 108 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 58
  108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 57 108 183 3 19 36 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 56 108 183
  (Polychromatic418967fa.accept_10_6_8_3_1_930 56 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 108 183 (Polychromatic418967fa.accept_10_5_8_3_1_229 55 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 108 183 3 18 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 108 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 53
  108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 108 183
  (Polychromatic418967fa.accept_16_4_12_7_1_4475 52 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 51 108 183 3 17 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 50 108 183 (Polychromatic418967fa.accept_16_2_12_7_1_3410 50 108 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 108 183
  (Polychromatic418967fa.accept_11_5_9_7_1_411 49 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 108 183 3 16 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 108 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 108 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 108 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 46
  108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 108 183 3 15 36 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 108 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 108 183 (Polychromatic418967fa.accept_8_3_4_7_1_475 43 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 108 183 3 14 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 108 183 (Polychromatic418967fa.accept_10_1_8_3_1_947
  41 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 108 183
  (Polychromatic418967fa.accept_7_5_3_1_1_424 40 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 108 183 3 13 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 108 183 (Polychromatic418967fa.accept_11_5_9_7_1_411 38 108 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 108 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 37
  108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 108 183 3 12 36 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 108 183
  (Polychromatic418967fa.accept_8_3_4_7_1_475 35 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 108 183 (Polychromatic418967fa.accept_16_2_12_7_1_3410 34 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 108 183 3 11 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 108 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 32
  108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 108 183
  (Polychromatic418967fa.accept_10_1_8_3_1_947 31 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 108 183 3 10 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 108 183 (Polychromatic418967fa.accept_13_3_4_1_1_363 29 108 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 108 183
  (Polychromatic418967fa.accept_17_11_6_13_1_10553 28 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 27 108 183 3 9 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 26 108 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 108 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 108 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 108 183 3 8 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 108 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 108 183 (Polychromatic418967fa.accept_19_3_13_12_1_10525 22
  108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 108 183 3 7 36 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 108 183
  (Polychromatic418967fa.accept_16_4_12_7_1_4475 20 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 108 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 108 183 3 6 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 108 183
  (Polychromatic418967fa.accept_21_17_3_15_1_5762 17 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 108 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 108 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 108 183 3 5 36 61 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 108 183
  (Polychromatic418967fa.accept_19_14_13_12_1_2259 14 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 108 183 (Polychromatic418967fa.accept_11_2_9_7_1_124 13 108 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 108 183 3 4 36 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 108 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 108 183 (Polychromatic418967fa.accept_13_10_4_1_1_2142 10 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 108 183 3 3 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 108 183 (Polychromatic418967fa.accept_16_8_12_7_1_2399 8 108 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 108 183
  (Polychromatic418967fa.accept_17_7_6_13_1_10548 7 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 108 183 3 2 36 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 108 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 108 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 108 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 108 183 3 1 36 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 108 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 108 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 108 183 (Polychromatic418967fa.accept_10_1_8_3_1_947 1 108 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 108
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 107 183 (Eq.refl
  Bool.true) (allA_succ_of_accept 76 107 183 (accept_3_4 76 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 107 183 (Polychromatic418967fa.accept_10_5_7_3_1_561 75 107 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 74 107 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 107 183 (accept_3_4 73 107 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 107 183 (Polychromatic418967fa.accept_13_7_3_1_1_814
  72 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 107 183
  (Polychromatic418967fa.accept_13_6_3_1_1_1413 71 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 107 183 (accept_3_4 70 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 107 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 69 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 107 183 (accept_3_4 67 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 107 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 107 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 65 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 107 183 (accept_3_4 64 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 107 183 (Polychromatic418967fa.accept_13_11_3_1_1_1397 63 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 62 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 107 183 (accept_3_4 61 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 107 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 60 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 107 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 59 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 107 183 (accept_3_4 58 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 107 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 57 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 107 183 (accept_3_4 55 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 107 183 (Polychromatic418967fa.accept_10_4_7_3_1_54 54 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 107 183
  (Polychromatic418967fa.accept_16_5_11_7_1_5635 53 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 107 183 (accept_3_4 52 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 107 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 51 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 50 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 107 183 (accept_3_4 49 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 107 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 107 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 47 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 107 183 (accept_3_4 46 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 107 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 45 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 107 183 (accept_3_4 43 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 107 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 42 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 107 183
  (Polychromatic418967fa.accept_7_6_2_1_1_214 41 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 107 183 (accept_3_4 40 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 107 183 (Polychromatic418967fa.accept_21_18_2_15_1_5737 39 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 38 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 107 183 (accept_3_4 37 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 107 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 36 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 107 183
  (Polychromatic418967fa.accept_10_5_7_3_1_561 35 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 107 183 (accept_3_4 34 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 107 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 107 183 (accept_3_4 31 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 107 183 (Polychromatic418967fa.accept_13_4_3_1_1_2898 30 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 107 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 107 183 (accept_3_4 28 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 107 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 26 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 107 183 (accept_3_4 25 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 107 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 107 183
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 107 183 (accept_3_4 22 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 107 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 21 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 107 183 (accept_3_4 19 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 107 183 (Polychromatic418967fa.accept_13_5_3_1_1_1398 18 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 107 183
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 107 183 (accept_3_4 16 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 107 183 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 14 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 107 183 (accept_3_4 13 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 107 183 (Polychromatic418967fa.accept_8_4_3_7_1_491 12 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 107 183
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 107 183 (accept_3_4 10 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  107 183 (Polychromatic418967fa.accept_12_9_11_3_1_772 9 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 107 183 (accept_3_4 7 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 107 183 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 107 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 107 183
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 107 183 (accept_3_4 4 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  107 183 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 107 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 107 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 2 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 107 183 (accept_3_4 1 107 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 107 183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 78 106 183 (Eq.refl Bool.true) (allA_succ_of_accept 77 106 183 (accept_3_5 77 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 76 106 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 76 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 106 183
  (Polychromatic418967fa.accept_19_18_11_12_1_6163 75 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 106 183 (accept_3_5 74 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 73 106 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 106 183 (Polychromatic418967fa.accept_14_2_8_1_1_1647 72 106
  183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 106 183 (accept_3_5 71 106
  183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 106 183
  (Polychromatic418967fa.accept_19_13_11_12_1_3447 70 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 69 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 106 183 (accept_3_5 68 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 67 106 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 67 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 106 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 66 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 106 183 (accept_3_5 65 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 106 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 64 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 106 183 (Polychromatic418967fa.accept_14_7_8_1_1_1621 63 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 106 183 (accept_3_5 62 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 106 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 106 183
  (Polychromatic418967fa.accept_9_6_7_3_1_436 60 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 106 183 (accept_3_5 59 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 106 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 58 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 57 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 106 183 (accept_3_5 56 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 55 106 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 55 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 106 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 54 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 106 183 (accept_3_5 53 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 106 183 (Polychromatic418967fa.accept_21_10_1_15_1_10541 52 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 106 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 51 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 106 183 (accept_3_5 50 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 49 106 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 106 183
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 48 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 106 183 (accept_3_5 47 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 106 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 46 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 45 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 106 183 (accept_3_5 44 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 106 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 43 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 106 183
  (Polychromatic418967fa.accept_9_6_7_3_1_436 42 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 106 183 (accept_3_5 41 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 106 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 106 183 (Polychromatic418967fa.accept_10_9_6_3_1_545 39 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 106 183 (accept_3_5 38 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 37 106 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 106 183
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 106 183 (accept_3_5 35 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 106 183 (Polychromatic418967fa.accept_15_4_1_3_1_1922 34 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 33 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 106 183 (accept_3_5 32 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 106 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 31 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 106 183
  (Polychromatic418967fa.accept_12_6_10_3_1_1313 30 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 106 183 (accept_3_5 29 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 106 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 106 183 (Polychromatic418967fa.accept_10_7_6_3_1_927 27 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 106 183 (accept_3_5 26 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 106 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 106 183
  (Polychromatic418967fa.accept_9_6_7_3_1_436 24 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 106 183 (accept_3_5 23 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 106 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 21 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 106 183 (accept_3_5 20 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 19 106 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 19 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 106 183
  (Polychromatic418967fa.accept_10_8_6_3_1_1394 18 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 106 183 (accept_3_5 17 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 106 183 (Polychromatic418967fa.accept_13_3_2_1_1_2907 16 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 106 183 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 106 183 (accept_3_5 14 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 106 183
  (Polychromatic418967fa.accept_13_12_2_1_1_2909 12 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 106 183 (accept_3_5 11 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 106 183 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 9 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 106 183 (accept_3_5 8 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 106 183 (Polychromatic418967fa.accept_6_1_4_3_1_14 7 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 106 183
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 106 183 (accept_3_5 5 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  106 183 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 106 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 106 183 (Polychromatic418967fa.accept_13_3_2_1_1_2907 3 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 106 183 (accept_3_5 2 106 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 106 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 106 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 106
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 105 183 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 105 183 3 26 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 105 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 77 105 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 105 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 76 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 105 183 3 25 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 105 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 105 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  73 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 105 183 3 24 35 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 105 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 71 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 70 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 105 183 3 23 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 105 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 68
  105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 105 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 67 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 105 183 3 22 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 105 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 65 105 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 105 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  64 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 105 183 3 21 35 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 105 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 62 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 105 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 61 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 105 183 3 20 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 105 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 59
  105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 105 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 58 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 105 183 3 19 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 105 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 56 105 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 105 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  55 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 105 183 3 18 35 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 105 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 53 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 105 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 52 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 105 183 3 17 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 50
  105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 105 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 49 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 105 183 3 16 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 105 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 47 105 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 46
  105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 105 183 3 15 35 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 105 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 44 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 105 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 43 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 105 183 3 14 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 105 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 41
  105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 105 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 40 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 105 183 3 13 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 105 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 105 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  37 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 105 183 3 12 35 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 105 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 35 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 34 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 105 183 3 11 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 105 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 32
  105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 105 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 31 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 105 183 3 10 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 105 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 105 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 105 183 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 105 183 3 9 35 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 105 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 26 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 105 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 105 183 3 8 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 105 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 23
  105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 105 183
  (Polychromatic418967fa.accept_4_2_1_3_1_27 22 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 105 183 3 7 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 105 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 105 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 105 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 105 183 3 6 35 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 105 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 105 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 105 183 3 5 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14
  105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 105 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 105 183 3 4 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 105 183 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 10 105 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 105 183 3 3 35 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 105 183
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 105 183 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 105 183 3 2 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 105 183 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 105 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 105 183
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 105 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 105 183 3 1 35 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 105 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 105 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 105 183 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 105 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 105
  183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 104 183 (Eq.refl
  Bool.true) (allA_succ_of_accept 79 104 183 (accept_3_4 79 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 78 104 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 78 104 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 104 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 77 104 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 104 183 (accept_3_4 76 104 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 104 183 (Polychromatic418967fa.accept_7_5_6_1_1_407
  75 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 104 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 74 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 104 183 (accept_3_4 73 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 104 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 72 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 104 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 71 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 104 183 (accept_3_4 70 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 104 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 69 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 104 183
  (Polychromatic418967fa.accept_7_5_6_1_1_407 68 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 104 183 (accept_3_4 67 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 104 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 66 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 104 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 65 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 104 183 (accept_3_4 64 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 104 183 (Polychromatic418967fa.accept_14_7_6_1_1_1656 63 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 104 183
  (Polychromatic418967fa.accept_9_8_5_3_1_777 62 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 104 183 (accept_3_4 61 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 104 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 60 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 104 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 59 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 104 183 (accept_3_4 58 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 104 183 (Polychromatic418967fa.accept_10_7_4_3_1_560 57 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 104 183
  (Polychromatic418967fa.accept_9_2_5_3_1_37 56 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 104 183 (accept_3_4 55 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 104 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 104 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 53 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 104 183 (accept_3_4 52 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 104 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 104 183
  (Polychromatic418967fa.accept_24_2_8_15_1_10536 50 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 104 183 (accept_3_4 49 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 104 183 (Polychromatic418967fa.accept_18_12_14_3_1_2655 48 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 104 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 47
  104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 104 183 (accept_3_4 46
  104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 104 183
  (Polychromatic418967fa.accept_18_9_14_3_1_6407 45 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 104 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 44 104 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 104 183 (accept_3_4 43 104 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 104 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 104 183 (Polychromatic418967fa.accept_6_5_2_3_1_81 41
  104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 104 183 (accept_3_4 40
  104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 104 183
  (Polychromatic418967fa.accept_10_9_4_3_1_539 39 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 104 183 (Polychromatic418967fa.accept_9_2_5_3_1_37 38 104 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 104 183 (accept_3_4 37 104 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 104 183 (Polychromatic418967fa.accept_16_4_8_7_1_3396 36 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 104 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 35 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 104 183 (accept_3_4 34 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 104 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 104 183 (Polychromatic418967fa.accept_15_2_14_3_1_1916 32 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 104 183 (accept_3_4 31 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 104 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 104 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 104 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 29 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 104 183 (accept_3_4 28 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 104 183 (Polychromatic418967fa.accept_10_7_4_3_1_560 27 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 104 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 26 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 104 183 (accept_3_4 25 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 104 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 104 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 23 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 104 183 (accept_3_4 22 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 104 183 (Polychromatic418967fa.accept_14_7_6_1_1_1656 21 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 104 183 (Polychromatic418967fa.accept_9_2_5_3_1_37 20 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 104 183 (accept_3_4 19 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 104 183 (Polychromatic418967fa.accept_12_6_8_3_1_82 18 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 104 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 17 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 104 183 (accept_3_4 16 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 104 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 104 183 (Polychromatic418967fa.accept_19_14_9_12_1_9113 14 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 104 183 (accept_3_4 13 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 104 183 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 104 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 104 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 11 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 104 183 (accept_3_4 10 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  104 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 104 183 (Polychromatic418967fa.accept_9_8_5_3_1_777 8 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 104 183 (accept_3_4 7 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 104 183 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 104 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 104 183
  (Polychromatic418967fa.accept_6_5_2_3_1_81 5 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 104 183 (accept_3_4 4 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  104 183 (Polychromatic418967fa.accept_19_3_9_12_1_6253 3 104 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 104 183 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 104 183 (accept_3_4 1 104 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 104 183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 81 103 183 (Eq.refl Bool.true) (allA_succ_of_accept 80 103 183 (accept_3_5 80 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 79 103 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 79 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 103 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 78 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 103 183 (accept_3_5 77 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  76 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 76 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 103 183 (Polychromatic418967fa.accept_21_12_19_15_1_8942 75 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 103 183 (accept_3_5 74 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 103 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 73 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 103 183
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 72 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 103 183 (accept_3_5 71 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 70 103 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 103 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 69 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 103 183 (accept_3_5 68 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 103 183 (Polychromatic418967fa.accept_7_4_5_1_1_418
  67 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 103 183
  (Polychromatic418967fa.accept_7_3_5_1_1_72 66 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 103 183 (accept_3_5 65 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  64 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 64 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 103 183 (Polychromatic418967fa.accept_11_8_4_7_1_1303 63 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 103 183 (accept_3_5 62 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 103 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 61 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 103 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 60 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 103 183 (accept_3_5 59 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  58 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 58 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 103 183 (Polychromatic418967fa.accept_12_9_7_3_1_1309 57 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 103 183 (accept_3_5 56 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 103 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 55 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 103 183
  (Polychromatic418967fa.accept_13_2_12_1_1_343 54 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 103 183 (accept_3_5 53 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  52 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 52 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 103 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 51 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 103 183 (accept_3_5 50 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 103 183 (Polychromatic418967fa.accept_19_11_8_12_1_6204 49 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 103 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 48 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 47 103 183 (accept_3_5 47 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  46 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 46 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 45 103 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 45 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 103 183 (accept_3_5 44 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 43 103 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 103 183
  (Polychromatic418967fa.accept_9_6_4_3_1_203 42 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 103 183 (accept_3_5 41 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 40 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 103 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 103 183 (accept_3_5 38 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 103 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 37 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 103 183
  (Polychromatic418967fa.accept_11_3_4_7_1_114 36 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 103 183 (accept_3_5 35 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 34 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 103 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 103 183 (accept_3_5 32 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 103 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 103 183
  (Polychromatic418967fa.accept_11_8_4_7_1_1303 30 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 103 183 (accept_3_5 29 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 28 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 103 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 103 183 (accept_3_5 26 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 25 103 183 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 103 183
  (Polychromatic418967fa.accept_7_3_5_1_1_72 24 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 103 183 (accept_3_5 23 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 22 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 103 183 (Polychromatic418967fa.accept_12_9_7_3_1_1309 21 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 103 183 (accept_3_5 20 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 103 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 103 183
  (Polychromatic418967fa.accept_7_4_5_1_1_418 18 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 103 183 (accept_3_5 17 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 16 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 103 183 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 103 183 (accept_3_5 14 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 103 183 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 103 183
  (Polychromatic418967fa.accept_15_12_13_3_1_1915 12 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 103 183 (accept_3_5 11 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 10 103 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 103 183 (Polychromatic418967fa.accept_12_9_7_3_1_1309 9 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 103 183 (accept_3_5 8 103 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 103 183 (Polychromatic418967fa.accept_9_7_4_3_1_204 7
  103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 103 183
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 103 183 (accept_3_5 5 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  103 183 (Polychromatic418967fa.accept_6_4_1_3_1_77 4 103 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 103 183 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 103 183 (accept_3_5 2 103 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 103 183 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 103 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 103
  183))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 102 183 (Eq.refl
  Bool.true) (allA_succ_of_gcd 81 102 183 3 27 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 80 102 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 80 102 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 102 183
  (Polychromatic418967fa.accept_16_15_6_7_1_4512 79 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 102 183 3 26 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 77 102 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 102 183
  (Polychromatic418967fa.accept_11_10_3_7_1_2564 76 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 75 102 183 3 25 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 74 102 183 (Polychromatic418967fa.accept_12_2_6_3_1_331 74 102 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 73
  102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 102 183 3 24 34 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 102 183
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 71 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 102 183 (Polychromatic418967fa.accept_11_4_3_7_1_828 70 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 69 102 183 3 23 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 68 102 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 68
  102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 102 183
  (Polychromatic418967fa.accept_14_11_4_1_1_4255 67 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 102 183 3 22 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 65 102 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 102 183 (Polychromatic418967fa.accept_12_4_6_3_1_332
  64 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 63 102 183 3 21 34 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 62 102 183
  (Polychromatic418967fa.accept_12_2_6_3_1_331 62 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 61 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 102 183 3 20 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 102 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 59
  102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 102 183
  (Polychromatic418967fa.accept_12_10_6_3_1_786 58 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 57 102 183 3 19 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 56 102 183 (Polychromatic418967fa.accept_12_8_6_3_1_366 56 102 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 102 183 (Polychromatic418967fa.accept_10_5_2_3_1_239
  55 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 102 183 3 18 34 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 102 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 53 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 102 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 52 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51 102 183 3 17 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 50 102 183 (Polychromatic418967fa.accept_12_2_6_3_1_331
  50 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 102 183
  (Polychromatic418967fa.accept_4_1_2_3_1_9 49 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 102 183 3 16 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 102 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 102 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 102 183 (Polychromatic418967fa.accept_12_10_6_3_1_786
  46 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 45 102 183 3 15 34 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 102 183
  (Polychromatic418967fa.accept_12_8_6_3_1_366 44 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 102 183 (Polychromatic418967fa.accept_11_10_3_7_1_2564 43 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 102 183 3 14 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 41
  102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 102 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 40 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 39 102 183 3 13 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 38 102 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 102 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 37
  102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 102 183 3 12 34 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 102 183
  (Polychromatic418967fa.accept_10_5_2_3_1_239 35 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 102 183 (Polychromatic418967fa.accept_12_10_6_3_1_786 34 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 102 183 3 11 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 102 183 (Polychromatic418967fa.accept_11_10_3_7_1_2564
  32 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 102 183
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 102 183 3 10 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 29 102 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 102 183 (Polychromatic418967fa.accept_12_4_6_3_1_332
  28 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 102 183 3 9 34 61
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 102 183
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 25 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 102 183 3 8 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 102 183
  (Polychromatic418967fa.accept_13_10_11_1_1_2152 23 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 102 183 (Polychromatic418967fa.accept_12_10_6_3_1_786 22 102 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 102 183 3 7 34 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 102 183
  (Polychromatic418967fa.accept_12_8_6_3_1_366 20 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 102 183 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 102 183 3 6 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 17
  102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 102 183
  (Polychromatic418967fa.accept_12_4_6_3_1_332 16 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 102 183 3 5 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 102 183 (Polychromatic418967fa.accept_12_2_6_3_1_331 14 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 13 102 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 102 183 3 4 34 61 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 102 183
  (Polychromatic418967fa.accept_10_1_2_3_1_1910 11 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 102 183 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 102 183 3 3 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 102 183 (Polychromatic418967fa.accept_12_8_6_3_1_366 8 102 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 102 183
  (Polychromatic418967fa.accept_13_7_11_1_1_2903 7 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 102 183 3 2 34 61 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 5 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 102 183 (Polychromatic418967fa.accept_11_4_3_7_1_828 4 102 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 102 183 3 1 34 61 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 102 183
  (Polychromatic418967fa.accept_12_2_6_3_1_331 2 102 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 102 183 (Polychromatic418967fa.accept_4_1_2_3_1_9 1 102 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 102
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 101 183 (Eq.refl
  Bool.true) (allA_succ_of_accept 82 101 183 (accept_3_4 82 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 101 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 101 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 101 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 80 101 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 101 183 (accept_3_4 79 101 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 78
  101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 101 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 77 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 101 183 (accept_3_4 76 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 101 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 75 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 74 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 101 183 (accept_3_4 73 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 101 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 101 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 71 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 101 183 (accept_3_4 70 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 101 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 69 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 101 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 68 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 101 183 (accept_3_4 67 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 66 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 101 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 65 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 101 183 (accept_3_4 64 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 101 183 (Polychromatic418967fa.accept_13_11_10_1_1_1409 63 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 62 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 101 183 (accept_3_4 61 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 101 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 101 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 59 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 101 183 (accept_3_4 58 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 101 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 57 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 101 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 56 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 101 183 (accept_3_4 55 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 54 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 54 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 101 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 53 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 101 183 (accept_3_4 52 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 101 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 51 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 50 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 101 183 (accept_3_4 49 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 101 183 (Polychromatic418967fa.accept_10_8_1_3_1_1374 48 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 101 183
  (Polychromatic418967fa.accept_7_5_3_1_1_424 47 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 101 183 (accept_3_4 46 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 101 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 45 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 101 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 44 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 101 183 (accept_3_4 43 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 42 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 101 183
  (Polychromatic418967fa.accept_9_5_2_3_1_194 41 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 101 183 (accept_3_4 40 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 101 183 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 38 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 101 183 (accept_3_4 37 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 101 183 (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 101 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 101 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 35 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 101 183 (accept_3_4 34 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 101 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 101 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 32 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 101 183 (accept_3_4 31 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 30 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 101 183
  (Polychromatic418967fa.accept_15_14_11_3_1_1957 29 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 101 183 (accept_3_4 28 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 101 183 (Polychromatic418967fa.accept_16_11_5_7_1_2395 27 101 183 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 26 101 183
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 101 183 (accept_3_4 25 101 183
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 101 183 (Polychromatic418967fa.accept_9_6_2_3_1_771
  24 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 101 183
  (Polychromatic418967fa.accept_7_2_3_1_1_10 23 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 101 183 (accept_3_4 22 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 101 183 (Polychromatic418967fa.accept_12_9_5_3_1_782 21 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 101 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 20 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 101 183 (accept_3_4 19 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 18 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 101 183
  (Polychromatic418967fa.accept_9_8_2_3_1_447 17 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 101 183 (accept_3_4 16 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 101 183 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 14 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 101 183 (accept_3_4 13 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 101 183 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 101 183
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 101 183 (accept_3_4 10 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  101 183 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 101 183 (Polychromatic418967fa.accept_6_2_5_3_1_16 8 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 101 183 (accept_3_4 7 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 6 101 183 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 101 183
  (Polychromatic418967fa.accept_7_5_3_1_1_424 5 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 101 183 (accept_3_4 4 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  101 183 (Polychromatic418967fa.accept_17_3_16_13_1_6635 3 101 183 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 101 183 (Polychromatic418967fa.accept_4_2_1_3_1_27 2 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 101 183 (accept_3_4 1 101 183 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 101
  183)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_183_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


