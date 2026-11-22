-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch210
-- name    : Polychromatic418967fa_Branch210
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:23:25.454557+00:00
-- url     : https://prove2.me/theorems/882edafa-4518-41df-a9e8-f3250adbb3b9
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch210_Segment001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_210 : allB 210 210 :=
  allB_succ' 2 209 210 (Eq.refl Bool.true) (allA_succ_of_accept 1 209 210 (accept_3_4 1 209 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 210)) (allB_succ' 3 208 210 (Eq.refl Bool.true) (allA_succ_of_gcd 2 208 210 2 1 104
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 208 210
  (Polychromatic418967fa.accept_41_1_3_5_1_12459 1 208 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 208 210))) (allB_succ' 4 207 210 (Eq.refl Bool.true) (allA_succ_of_gcd 3 207 210 3 1 69 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 207 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 207 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 207 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 207 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 210)))) (allB_succ' 5 206 210 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  206 210 2 2 103 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 206 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 3 206 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 206 210 2 1 103 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 206 210 (accept_3_4 1 206 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 206 210))))) (allB_succ' 6 205 210 (Eq.refl Bool.true) (allA_succ_of_gcd 5 205 210 5 1
  41 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 205 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 4 205 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 205 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 205 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 205 210 (accept_3_5 2 205 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 205 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 205 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 205 210)))))) (allB_succ' 7 204 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 204 210 6 1 34 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 204 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 204 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 204 210 2 2 102 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 204 210 3 1 68 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 204 210 2 1 102 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 204 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 204 210))))))) (allB_succ' 8 203 210 (Eq.refl Bool.true) (allA_succ_of_gcd 7 203 210 7 1 29 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 203 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 6 203 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 203 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 210 (accept_3_4 4 203 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 203 210 (Polychromatic418967fa.accept_24_3_11_18_1_12458 3 203 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 203 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 203 210 (accept_3_4 1 203 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203
  210)))))))) (allB_succ' 9 202 210 (Eq.refl Bool.true) (allA_succ_of_gcd 8 202 210 2 4 101 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 202 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 202 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 202 210 2 3 101 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 202 210 (accept_3_5 5 202 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 202 210 2 2 101 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 202 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 202 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 202 210 2 1 101 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 202 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 1 202 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 202 210))))))))) (allB_succ' 10 201 210 (Eq.refl Bool.true) (allA_succ_of_gcd 9 201 210 3 3 67 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 201 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 201 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 201 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 201 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 201 210 3 2 67 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 201 210 (Polychromatic418967fa.accept_20_5_1_10_1_6523 5 201 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 4 201 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 201 210 3 1 67 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 201 210 (Polychromatic418967fa.accept_11_2_3_1_1_244 2 201 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 210 (Polychromatic418967fa.accept_13_1_6_2_1_377 1 201 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 210)))))))))) (allB_succ' 11 200 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 10 200 210 10 1 20 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 210 (Polychromatic418967fa.accept_12_9_8_6_1_466 9 200 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 200 210 2 4 100 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 200 210 (accept_3_4 7
  200 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 200 210 2 3 100 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 200 210 5 1 40 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 200 210 2 2 100 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 210
  (Polychromatic418967fa.accept_11_3_2_1_1_994 3 200 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 210 2 1 100 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 210 (accept_3_4 1 200 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  210))))))))))) (allB_succ' 12 199 210 (Eq.refl Bool.true) (allA_succ_of_accept 11 199 210 (accept_3_5 11 199 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 199 210
  (Polychromatic418967fa.accept_17_10_12_6_1_4917 10 199 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 199 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 199 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 199 210 (accept_3_5 8 199 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 199 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 199 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 199 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 6 199 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 199 210 (accept_3_5 5 199 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  199 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 199 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 199 210 (Polychromatic418967fa.accept_18_3_1_12_1_4419 3 199 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 199 210 (accept_3_5 2 199 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 199 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 199 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 199 210)))))))))))) (allB_succ' 13 198 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 12 198 210 6 2 33 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 198 210 (Polychromatic418967fa.accept_13_11_3_2_1_863 11 198 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 198 210 2 5 99 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 198 210 3 3 66 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 198 210 2 4 99 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 210
  (Polychromatic418967fa.accept_19_7_8_1_1_4028 7 198 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 198 210 6 1 33 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 198 210 (Polychromatic418967fa.accept_13_5_3_2_1_1499 5 198 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 198 210 2 2 99 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 198 210 3 1 66 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 198 210 2 1 99 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 210 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1
  198 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 198 210))))))))))))) (allB_succ' 14 197
  210 (Eq.refl Bool.true) (allA_succ_of_accept 13 197 210 (accept_3_4 13 197 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 197 210 (Polychromatic418967fa.accept_17_12_10_6_1_3691 12 197 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 197 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 197 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 197 210 (accept_3_4 10 197 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  197 210 (Polychromatic418967fa.accept_11_9_10_1_1_581 9 197 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 197 210 (Polychromatic418967fa.accept_19_8_7_1_1_6801 8 197 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 210 (accept_3_4 7 197 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 197 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 197 210
  (Polychromatic418967fa.accept_9_5_8_3_1_437 5 197 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 197 210 (accept_3_4 4 197 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  197 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 197 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 197 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 197 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 210 (accept_3_4 1 197 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 197 210)))))))))))))) (allB_succ' 15 196 210 (Eq.refl Bool.true) (allA_succ_of_gcd 14
  196 210 14 1 14 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 13 196 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 196 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 196 210 2 6 98 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 196 210 (accept_3_5 11 196 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 10 196 210 2 5 98 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 196 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 196 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 196 210 2 4 98 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 7 196 210 7 1 28 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 6 196 210 2 3 98 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 196 210 (accept_3_5 5
  196 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 196 210 2 2 98 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 196 210
  (Polychromatic418967fa.accept_12_3_4_6_1_434 3 196 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 196 210 2 1 98 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 196 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 196 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 196 210))))))))))))))) (allB_succ' 16 195 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 195 210 15 1 13 14 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 14 195 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 14 195 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 195 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  195 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 195 210 3 4 65 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 195 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 195 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 195 210 5 2 39 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 9 195 210 3 3 65 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 195 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 8 195 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 195 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 7 195 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 195 210 3 2 65 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 195 210 5 1 39 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 195 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 195 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 195 210 3 1 65 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 195 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 195 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 195 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 195 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195 210)))))))))))))))) (allB_succ' 17 194 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 16 194 210 2 8 97 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 194 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 194 210 2 7 97 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 194 210 (accept_3_4 13
  194 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 194 210 2 6 97 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 194 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 11 194 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 194 210 2 5 97 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 194 210 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 194 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 194 210 2 4 97 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 194 210 (accept_3_4 7 194 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194 210 2 3 97 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 194 210 (Polychromatic418967fa.accept_13_5_12_2_1_1423
  5 194 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 194 210 2 2 97 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 194 210
  (Polychromatic418967fa.accept_12_3_2_6_1_138 3 194 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 194 210 2 1 97 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 194 210 (accept_3_4 1 194 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194
  210))))))))))))))))) (allB_succ' 18 193 210 (Eq.refl Bool.true) (allA_succ_of_accept 17 193 210 (accept_3_5 17 193 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 193 210 (Polychromatic418967fa.accept_9_7_4_3_1_204
  16 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 193 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 193 210 (accept_3_5 14 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 193 210 (Polychromatic418967fa.accept_22_13_17_12_1_12457 13 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 193 210 (Polychromatic418967fa.accept_16_12_1_2_1_2163 12 193 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 193 210 (accept_3_5 11 193 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 193 210 (Polychromatic418967fa.accept_9_1_4_3_1_201
  10 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 193 210
  (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 193 210 (accept_3_5 8 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  193 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 193 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 193 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 193 210 (accept_3_5 5 193 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 193 210 (Polychromatic418967fa.accept_13_4_11_2_1_1458 4 193 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 193 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 193 210 (accept_3_5 2 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  193 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 193 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 193 210)))))))))))))))))) (allB_succ' 19 192 210 (Eq.refl Bool.true) (allA_succ_of_gcd 18 192
  210 6 3 32 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17
  192 210 (Polychromatic418967fa.accept_11_6_5_1_1_586 17 192 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 16 192 210 2 8 96 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 15 192 210 3 5 64 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 14 192 210 2 7 96 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 192 210 (Polychromatic418967fa.accept_19_13_2_1_1_4054 13 192
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 192 210 6 2 32 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 192 210
  (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 192 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 192 210 2 5 96 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 192 210 3 3 64 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 192 210 2 4 96 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 192 210 (Polychromatic418967fa.accept_19_7_2_1_1_4076 7 192 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192 210 6 1 32 35 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 192 210
  (Polychromatic418967fa.accept_13_5_10_2_1_856 5 192 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 192 210 2 2 96 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 192 210 3 1 64 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 192 210 2 1 96 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 192 210 (Polychromatic418967fa.accept_17_1_5_6_1_3717 1 192 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 192 210))))))))))))))))))) (allB_succ' 20 191 210 (Eq.refl Bool.true)
  (allA_succ_of_accept 19 191 210 (accept_3_4 19 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 210 (Polychromatic418967fa.accept_13_5_9_2_1_1489 18 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 191 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 210 (accept_3_4 16 191 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 15 191 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 210 (accept_3_4 13 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 210 (Polychromatic418967fa.accept_16_12_15_2_1_6473 12 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 210 (Polychromatic418967fa.accept_13_11_9_2_1_2969 11 191 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 210 (accept_3_4 10 191 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 210 (accept_3_4 7 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 210 (accept_3_4 4 191 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 210 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 191 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 210
  (Polychromatic418967fa.accept_17_2_4_6_1_1619 2 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 210 (accept_3_4 1 191 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  210)))))))))))))))))))) (allB_succ' 21 190 210 (Eq.refl Bool.true) (allA_succ_of_gcd 20 190 210 10 2 19 21 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 190 210
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 190 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 190 210 2 9 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 190 210 (accept_3_5 17 190 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 190 210 2 8 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 190 210 5 3 38 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 190 210 2 7 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 190 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 190 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 190 210 2 6 95 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 190 210 (accept_3_5 11 190 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 190 210 10 1 19 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 190 210
  (Polychromatic418967fa.accept_12_9_10_6_1_872 9 190 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 190 210 2 4 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 190 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 7 190 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 190 210 2 3 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 190 210 5 1 38 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 190 210 2 2 95 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 190 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 3
  190 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 190 210 2 1 95 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 190 210
  (Polychromatic418967fa.accept_17_1_3_6_1_3672 1 190 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 190 210))))))))))))))))))))) (allB_succ' 22 189 210 (Eq.refl Bool.true) (allA_succ_of_gcd 21 189 210 21 1 9
  10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 189 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 20 189 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 189 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 189 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 189 210 3 6 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 189 210
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 17 189 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 189 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 189 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 189 210 3 5 63 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 189 210 7 2 27 30 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 189 210
  (Polychromatic418967fa.accept_17_13_2_6_1_3683 13 189 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 189 210 3 4 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 189 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 189 210 (Polychromatic418967fa.accept_11_10_2_1_1_1036 10 189
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 189 210 3 3 63 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 189 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 189 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 7 189 210 7 1 27 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 189 210 3 2 63 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 189 210 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 189 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 189 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 189 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 189 210 3 1 63 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 189 210
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 189 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 189 210 (Polychromatic418967fa.accept_17_1_2_6_1_818 1 189 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 189 210)))))))))))))))))))))) (allB_succ' 23 188 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 22 188 210 2 11 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 188 210 (Polychromatic418967fa.accept_12_9_8_6_1_466 21 188 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 188 210 2 10 94 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 188 210 (accept_3_4 19 188 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 188 210 2 9 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 188 210 (Polychromatic418967fa.accept_13_4_6_2_1_1437
  17 188 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 210 2 8 94 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 210
  (Polychromatic418967fa.accept_9_6_8_3_1_183 15 188 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 210 2 7 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 210 (accept_3_4 13 188 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 210 2 6 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 11 188 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 210 2 5 94 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 188 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 210 2 4 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 210 (accept_3_4 7 188 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  210 2 3 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 5 188 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 210 2 2 94 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 188 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 210 2 1 94 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 210 (accept_3_4 1 188 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188 210))))))))))))))))))))))) (allB_succ' 24 187 210 (Eq.refl
  Bool.true) (allA_succ_of_accept 23 187 210 (accept_3_5 23 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 187 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 187 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 187 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 187 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 187 210 (accept_3_5 20 187 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 187 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 19
  187 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 187 210
  (Polychromatic418967fa.accept_20_18_7_10_1_3596 18 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 187 210 (accept_3_5 17 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 187 210 (Polychromatic418967fa.accept_13_3_5_2_1_1475 16 187 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 187 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 187 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 187 210 (accept_3_5 14 187 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 187 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13
  187 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 187 210
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 12 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 187 210 (accept_3_5 11 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 187 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 187 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 187 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 187 210 (accept_3_5 8 187 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 7 187 210 (Polychromatic418967fa.accept_13_7_5_2_1_401 7 187 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 187 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 6 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 187 210 (accept_3_5 5 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  187 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 187 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 187 210 (Polychromatic418967fa.accept_13_3_5_2_1_1475 3 187 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 187 210 (accept_3_5 2 187 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 187 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 187 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 187 210)))))))))))))))))))))))) (allB_succ' 25 186 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 24 186 210 6 4 31 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 186 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 23 186 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 210 2 11 93 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 186 210 3 7 62 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 186 210 2 10 93 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 186 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 19 186 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 210 6 3 31 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 186 210 (Polychromatic418967fa.accept_9_8_6_3_1_457 17 186 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 210 2 8 93 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 186 210 3 5 62 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 186 210 2 7 93 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 186 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 186 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 210 6 2 31 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 186 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 11 186 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 210 2 5 93 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 186 210 3 3 62 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 186 210 2 4 93 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 186 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 7
  186 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186 210 6 1 31 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 186 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 5 186 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 186 210 2 2 93 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 186 210 3 1 62 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 186 210 2 1 93 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 186 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 186 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 186 210))))))))))))))))))))))))) (allB_succ' 26 185 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 25 185 210 5 5 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 24 185 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 185 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 185 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 185 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 210 (accept_3_4 22 185 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 210
  (Polychromatic418967fa.accept_11_10_9_1_1_2186 21 185 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 185 210 5 4 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 185 210 (accept_3_4 19 185 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 210 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 185 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 185 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 210 (accept_3_4 16 185 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 15 185 210 5 3 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 185 210 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 185
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 185 210 (accept_3_4 13 185
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 185 210
  (Polychromatic418967fa.accept_13_12_3_2_1_1470 12 185 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 185 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 185 210 5 2 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 185 210 (Polychromatic418967fa.accept_13_9_3_2_1_399 9
  185 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 185 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 210 (accept_3_4 7 185 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 185 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 5 185 210 5 1 37 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 4 185 210 (accept_3_4 4 185 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 185 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 2 185 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 185 210 (accept_3_4 1 185 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185 210)))))))))))))))))))))))))) (allB_succ' 27 184 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 184 210 2 13 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 184 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 25 184 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 184 210 2 12 92 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 184 210 (accept_3_5 23 184 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 184 210 2 11 92 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 184 210
  (Polychromatic418967fa.accept_12_9_4_6_1_460 21 184 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 184 210 2 10 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 184 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 19 184 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 184 210 2 9 92 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 184 210 (accept_3_5 17 184 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 184 210 2 8 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 184 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 15
  184 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 184 210 2 7 92 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 184 210
  (Polychromatic418967fa.accept_25_13_9_10_1_12456 13 184 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 184 210 2 6 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 184 210 (accept_3_5 11 184 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 184 210 2 5 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 184 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 184 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 184 210 2 4 92 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 184 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 184 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 184 210 2 3 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 184 210 (accept_3_5 5 184 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 184
  210 2 2 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  184 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 184 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 184 210 2 1 92 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 184 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 184 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 184 210))))))))))))))))))))))))))) (allB_succ' 28 183
  210 (Eq.refl Bool.true) (allA_succ_of_gcd 27 183 210 3 9 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 183 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 26 183 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 183 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 183 210 3 8 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 183 210 (Polychromatic418967fa.accept_19_4_12_1_1_3991 23 183 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 183
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 183 210 3 7 61 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 183 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 183 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 183 210 (Polychromatic418967fa.accept_13_6_1_2_1_1464 19 183 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 183 210 3 6 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 183 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  183 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 183 210
  (Polychromatic418967fa.accept_12_4_3_6_1_879 16 183 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 183 210 3 5 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 183 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 183 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 183 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 183 210 3 4 61 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 183 210
  (Polychromatic418967fa.accept_16_11_7_2_1_4185 11 183 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 183 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 183 210 3 3 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 183 210 (Polychromatic418967fa.accept_12_8_3_6_1_909 8 183 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 210
  (Polychromatic418967fa.accept_17_7_13_6_1_811 7 183 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 183 210 3 2 61 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 183 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 183 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 4 183 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 183 210 3 1 61 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 183 210
  (Polychromatic418967fa.accept_12_2_3_6_1_112 2 183 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 183 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 183 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 183 210)))))))))))))))))))))))))))) (allB_succ' 29 182 210 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 182 210 14 2 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 182 210 (Polychromatic418967fa.accept_11_5_6_1_1_988 27 182 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 182 210 2 13 91 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 182 210 (accept_3_4 25 182 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 182 210 2 12 91 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 182 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 23 182 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 182 210 2 11 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 182 210 7 3 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 182 210 2 10 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 182 210 (accept_3_4 19 182 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 210 2 9 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 182 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 210 2 8 91 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 210
  (Polychromatic418967fa.accept_9_6_2_3_1_771 15 182 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 210 14 1 13 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 210 (accept_3_4 13 182 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 210 2 6 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 210 (Polychromatic418967fa.accept_16_11_6_2_1_4155 11 182 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 210 2 5 91 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 210
  (Polychromatic418967fa.accept_12_9_2_6_1_455 9 182 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 210 2 4 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 7 182 210 7 1 26 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 6 182 210 2 3 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 182 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 182 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 182 210 2 2 91 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 182 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 3
  182 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 210 2 1 91 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 210 (accept_3_4 1
  182 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 210))))))))))))))))))))))))))))) (allB_succ' 30 181 210
  (Eq.refl Bool.true) (allA_succ_of_accept 29 181 210 (accept_3_5 29 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 181 210 (Polychromatic418967fa.accept_11_6_5_1_1_586 28 181 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 181 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 181 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 181 210 (accept_3_5 26 181 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 181 210 (Polychromatic418967fa.accept_9_7_1_3_1_443
  25 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 181 210
  (Polychromatic418967fa.accept_9_6_1_3_1_191 24 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 181 210 (accept_3_5 23 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 181 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 22 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 181 210 (Polychromatic418967fa.accept_17_4_11_6_1_3730 21 181 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 181 210 (accept_3_5 20 181 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 181 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 181 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 181 210
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 181 210 (accept_3_5 17 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 181 210 (Polychromatic418967fa.accept_9_7_1_3_1_443 16 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 181 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 181 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 181 210 (accept_3_5 14 181 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 181 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 13 181 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 181 210
  (Polychromatic418967fa.accept_17_12_11_6_1_3729 12 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 181 210 (accept_3_5 11 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 181 210 (Polychromatic418967fa.accept_13_10_12_2_1_1460 10 181 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 181 210 (Polychromatic418967fa.accept_19_9_10_1_1_8329
  9 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 181 210 (accept_3_5 8
  181 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 181 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 7 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 181 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 6 181 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 181 210 (accept_3_5 5 181 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 181 210 (Polychromatic418967fa.accept_9_4_1_3_1_190 4 181 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 181 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3
  181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 181 210 (accept_3_5 2 181
  210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 181 210
  (Polychromatic418967fa.accept_13_1_12_2_1_384 1 181 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 181 210)))))))))))))))))))))))))))))) (allB_succ' 31 180 210 (Eq.refl Bool.true) (allA_succ_of_gcd 30 180
  210 30 1 6 7 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  180 210 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 180 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 180 210 2 14 90 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 27 180 210 3 9 60 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 26 180 210 2 13 90 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 180 210 5 5 36 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 180 210 6 4 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 180 210 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 180
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 210 2 11 90 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 180 210 3 7 60 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 180 210 10 2 18 21
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 180 210
  (Polychromatic418967fa.accept_11_8_4_1_1_1000 19 180 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 210 6 3 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 180 210 (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 180 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 210 2 8 90 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 180 210 15 1 12 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 180 210 2 7 90 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 180 210
  (Polychromatic418967fa.accept_22_13_4_12_1_9211 13 180 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 180 210 6 2 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 180 210 (Polychromatic418967fa.accept_19_11_9_1_1_2809 11 180 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 210 10 1 18 21 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 180 210 3 3 60 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 180 210 2 4 90 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 180 210
  (Polychromatic418967fa.accept_23_7_19_3_1_12427 7 180 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 210 6 1 30 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 5 180 210 5 1 36 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 4 180 210 2 2 90 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 180 210 3 1 60 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 180 210 2 1 90 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 180 210 (Polychromatic418967fa.accept_22_1_4_12_1_12446 1 180 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 180 210))))))))))))))))))))))))))))))) (allB_succ' 32 179 210 (Eq.refl
  Bool.true) (allA_succ_of_accept 31 179 210 (accept_3_4 31 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 179 210 (Polychromatic418967fa.accept_19_11_8_1_1_801 30 179 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 179 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 210 (accept_3_4 28 179 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 210
  (Polychromatic418967fa.accept_18_9_17_12_1_462 27 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 179 210 (Polychromatic418967fa.accept_19_7_8_1_1_4028 26 179 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 210 (accept_3_4 25 179 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 179 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 24 179 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 210 (Polychromatic418967fa.accept_9_5_8_3_1_437
  23 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 210 (accept_3_4 22
  179 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 21 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 179 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 20 179 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 210 (accept_3_4 19 179 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 179 210 (Polychromatic418967fa.accept_13_5_10_2_1_856 18 179 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 210 (accept_3_4 16 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 15 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 210 (Polychromatic418967fa.accept_9_5_8_3_1_437 14 179 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 210 (accept_3_4 13 179 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 210 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 179 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 210 (accept_3_4 10 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 210 (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 179 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 210 (accept_3_4 7 179 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 6 179 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 210 (accept_3_4 4 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 210 (Polychromatic418967fa.accept_13_3_10_2_1_381 3 179 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 210 (Polychromatic418967fa.accept_9_2_8_3_1_181 2 179 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 210 (accept_3_4 1 179 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179 210)))))))))))))))))))))))))))))))) (allB_succ' 33 178 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 32 178 210 2 16 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 178 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 31 178 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 178 210 2 15 89 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 178 210 (accept_3_5 29 178 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 178 210 2 14 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 178 210 (Polychromatic418967fa.accept_12_3_10_6_1_442
  27 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 178 210 2 13 89 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 178 210
  (Polychromatic418967fa.accept_11_3_2_1_1_994 25 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 178 210 2 12 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 178 210 (accept_3_5 23 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 178 210 2 11 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 178 210 (Polychromatic418967fa.accept_11_10_2_1_1_1036 21 178 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 178 210 2 10 89 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 178 210
  (Polychromatic418967fa.accept_9_1_7_3_1_41 19 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 178 210 2 9 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 178 210 (accept_3_5 17 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 178 210 2 8 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 178 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 15 178 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 178 210 2 7 89 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 178 210
  (Polychromatic418967fa.accept_9_4_7_3_1_43 13 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 178 210 2 6 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 178 210 (accept_3_5 11 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 178 210 2 5 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 178 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 178 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 178 210 2 4 89 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 178 210
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 178 210 2 3 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 178 210 (accept_3_5 5 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 178
  210 2 2 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  178 210 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 178 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 178 210 2 1 89 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 178 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 178 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 178 210))))))))))))))))))))))))))))))))) (allB_succ' 34
  177 210 (Eq.refl Bool.true) (allA_succ_of_gcd 33 177 210 3 11 59 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 177 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 32 177 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 31 177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 177 210 3 10 59 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 177 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 29 177 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 210 (Polychromatic418967fa.accept_9_1_6_3_1_177
  28 177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 177 210 3 9 59 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 177 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 26 177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 177 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 177 210 3 8 59 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 177 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 22 177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 177 210 3 7 59 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 20 177 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 20 177 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 177 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 177 210 3 6 59 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 177 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 16 177 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 177 210 3 5 59 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 177 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 14
  177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 13 177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 177 210 3 4 59 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 177 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 177 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 10 177 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 177 210 3 3 59 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 177 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 8 177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 177 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 177 210 3 2 59 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 177 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 177 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 210
  (Polychromatic418967fa.accept_9_4_6_3_1_179 4 177 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 177 210 3 1 59 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 177 210 (Polychromatic418967fa.accept_9_2_6_3_1_178 2 177 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 1 177 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177 210))))))))))))))))))))))))))))))))))
  (allB_succ' 35 176 210 (Eq.refl Bool.true) (allA_succ_of_gcd 34 176 210 2 17 88 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 33 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 176 210 2 16 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 176 210 (accept_3_4 31 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 176 210 2 15 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 176 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 29 176 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 210 2 14 88 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 210
  (Polychromatic418967fa.accept_12_3_8_6_1_895 27 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 176 210 2 13 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 176 210 (accept_3_4 25 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 210 2 12 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 176 210 (Polychromatic418967fa.accept_19_4_5_1_1_4077 23 176 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 210 2 11 88 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 21 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 210 2 10 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 176 210 (accept_3_4 19 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 210 2 9 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 17 176 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 210 2 8 88 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 210
  (Polychromatic418967fa.accept_9_6_5_3_1_205 15 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 210 2 7 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 210 (accept_3_4 13 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 210 2 6 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 176 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 176 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 210 2 5 88 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 210
  (Polychromatic418967fa.accept_12_9_8_6_1_466 9 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 210 2 4 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 210 (accept_3_4 7 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  210 2 3 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 210 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 176 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 210 2 2 88 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 176 210 (Polychromatic418967fa.accept_12_3_8_6_1_895 3 176 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 210 2 1 88 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 210 (accept_3_4 1 176 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 210))))))))))))))))))))))))))))))))))) (allB_succ' 36 175 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 35 175 210 35 1 5 6 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 34 175 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 34 175 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 175 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 175 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 175 210 (accept_3_5 32 175 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 175 210 (Polychromatic418967fa.accept_11_9_10_1_1_581 31 175 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 175 210 5 6 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 175 210 (accept_3_5 29 175 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 175 210 7 4 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 175 210 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 175 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 175 210 (accept_3_5 26 175 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 25 175 210 5 5 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 24 175 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 24 175 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 175 210 (accept_3_5 23 175 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 175 210 (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 175
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 175 210 7 3 25 30 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 175 210 5 4 35 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 175 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 175 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 175 210 (Polychromatic418967fa.accept_17_1_5_6_1_3717 18 175 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 175 210 (accept_3_5 17 175 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 175 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 16 175 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 175 210 5 3 35 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 175 210 7 2 25 30 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 175 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 13 175 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 175 210 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 175 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 175 210 (accept_3_5 11 175 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 175 210 5 2 35 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 175 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 175 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 175 210 (accept_3_5 8 175 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 7 175 210 7 1 25 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 6 175 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 6 175 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 5 175 210 5 1 35 42 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 175 210
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 175 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 3 175 210 (Polychromatic418967fa.accept_16_3_15_2_1_6475 3 175 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 175 210 (accept_3_5 2 175 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 175 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 175 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 175 210)))))))))))))))))))))))))))))))))))) (allB_succ' 37 174 210
  (Eq.refl Bool.true) (allA_succ_of_gcd 36 174 210 6 6 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 174 210 (Polychromatic418967fa.accept_13_9_5_2_1_2185 35 174 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 210 2 17 87 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 174 210 3 11 58 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 174 210 2 16 87 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 174 210
  (Polychromatic418967fa.accept_20_11_14_10_1_2320 31 174 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 174 210 6 5 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 174 210 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 174 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 210 2 14 87 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 174 210 3 9 58 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 174 210 2 13 87 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 174 210
  (Polychromatic418967fa.accept_13_12_5_2_1_2173 25 174 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 210 6 4 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 174 210 (Polychromatic418967fa.accept_13_10_5_2_1_1477 23 174 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 210 2 11 87 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 174 210 3 7 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 174 210 2 10 87 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 174 210
  (Polychromatic418967fa.accept_17_2_4_6_1_1619 19 174 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 210 6 3 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 174 210 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 174 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 210 2 8 87 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 174 210 3 5 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 174 210 2 7 87 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 174 210
  (Polychromatic418967fa.accept_24_13_6_18_1_12332 13 174 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 174 210 6 2 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 174 210 (Polychromatic418967fa.accept_17_11_4_6_1_2631 11 174 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 210 2 5 87 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 174 210 3 3 58 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 174 210 2 4 87 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 174 210
  (Polychromatic418967fa.accept_13_7_5_2_1_401 7 174 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 174 210 6 1 29 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 174 210 (Polychromatic418967fa.accept_17_5_4_6_1_7342 5 174 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 174 210 2 2 87 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 174 210 3 1 58 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 174 210 2 1 87 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 210
  (Polychromatic418967fa.accept_20_1_14_10_1_12443 1 174 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 174 210))))))))))))))))))))))))))))))))))))) (allB_succ' 38 173 210 (Eq.refl Bool.true)
  (allA_succ_of_accept 37 173 210 (accept_3_4 37 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 210 (Polychromatic418967fa.accept_23_13_12_3_1_12455 36 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 173 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 173 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 210 (accept_3_4 34 173 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 33 173 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 32 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 210 (accept_3_4 31 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 210 (Polychromatic418967fa.accept_24_6_5_18_1_3621 30 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 173 210 (Polychromatic418967fa.accept_20_9_13_10_1_452 29 173 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 210 (accept_3_4 28 173 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 173 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 26 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 210 (accept_3_4 25 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 24 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 210 (accept_3_4 22 173 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 210 (Polychromatic418967fa.accept_16_5_13_2_1_2138 21 173 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 210
  (Polychromatic418967fa.accept_22_20_19_12_1_12454 20 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 173 210 (accept_3_4 19 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 173 210 (Polychromatic418967fa.accept_13_5_4_2_1_846 18 173 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 173 210 (Polychromatic418967fa.accept_9_8_2_3_1_447 17 173 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 210 (accept_3_4 16 173 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 15
  173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 210
  (Polychromatic418967fa.accept_9_5_2_3_1_194 14 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 210 (accept_3_4 13 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 210 (Polychromatic418967fa.accept_13_12_4_2_1_2955 12 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 210 (accept_3_4 10 173 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 210 (Polychromatic418967fa.accept_17_9_3_6_1_11232 9 173 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 210
  (Polychromatic418967fa.accept_9_8_2_3_1_447 8 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 210 (accept_3_4 7 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 210 (Polychromatic418967fa.accept_9_6_2_3_1_771 6 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 210 (Polychromatic418967fa.accept_9_5_2_3_1_194 5 173 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 210 (accept_3_4 4 173 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 210
  (Polychromatic418967fa.accept_20_2_13_10_1_11013 2 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 1 173 210 (accept_3_4 1 173 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one
  173 210)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 172 210 (Eq.refl Bool.true) (allA_succ_of_gcd 38 172 210
  2 19 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37
  172 210 (Polychromatic418967fa.accept_13_11_3_2_1_863 37 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 172 210 2 18 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 172 210 (accept_3_5 35 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 172 210 2 17 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 172 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 33 172 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 172 210 2 16 86 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 172 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 31 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 172 210 2 15 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 172 210 (accept_3_5 29 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 172 210 2 14 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 172 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 27 172 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 172 210 2 13 86 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 172 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 25 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 172 210 2 12 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 172 210 (accept_3_5 23 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 172 210 2 11 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 172 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 21 172 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 172 210 2 10 86 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 172 210
  (Polychromatic418967fa.accept_31_19_17_24_1_12453 19 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 172 210 2 9 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 172 210 (accept_3_5 17 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 172 210 2 8 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 172 210 (Polychromatic418967fa.accept_9_6_1_3_1_191 15 172 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 172 210 2 7 86 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 172 210
  (Polychromatic418967fa.accept_9_4_1_3_1_190 13 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 172 210 2 6 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 172 210 (accept_3_5 11 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 172 210 2 5 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 172 210 (Polychromatic418967fa.accept_12_9_4_6_1_460 9 172 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 172 210 2 4 86 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 172 210
  (Polychromatic418967fa.accept_9_7_1_3_1_443 7 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 172 210 2 3 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 172 210 (accept_3_5 5 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 172
  210 2 2 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  172 210 (Polychromatic418967fa.accept_12_3_4_6_1_434 3 172 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 172 210 2 1 86 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 172 210 (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 172 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 172 210)))))))))))))))))))))))))))))))))))))))
  (allB_succ' 40 171 210 (Eq.refl Bool.true) (allA_succ_of_gcd 39 171 210 3 13 57 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 171 210
  (Polychromatic418967fa.accept_11_5_6_1_1_988 38 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 171 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 37 171 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 171 210 3 12 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 171 210
  (Polychromatic418967fa.accept_18_17_9_12_1_2160 35 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 171 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 34 171 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 171 210 3 11 57 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 171 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 32 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 171 210 (Polychromatic418967fa.accept_22_9_17_12_1_12452 31 171 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 171 210 3 10 57 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 171 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 210 (Polychromatic418967fa.accept_12_4_3_6_1_879 28 171 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 171 210 3 9 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 171 210 (Polychromatic418967fa.accept_12_2_3_6_1_112
  26 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 210
  (Polychromatic418967fa.accept_4_1_3_2_1_3 25 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 171 210 3 8 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 171 210 (Polychromatic418967fa.accept_16_7_11_2_1_3117 23 171 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 171 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 22 171
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 171 210 3 7 57 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 171 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 20 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 171 210 (Polychromatic418967fa.accept_17_2_1_6_1_3777 19 171 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 171 210 3 6 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 171 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17
  171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 171 210
  (Polychromatic418967fa.accept_11_5_6_1_1_988 16 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 171 210 3 5 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 171 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 14 171 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 13 171 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 171 210 3 4 57 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 171 210
  (Polychromatic418967fa.accept_18_11_9_12_1_4427 11 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 171 210 (Polychromatic418967fa.accept_12_10_3_6_1_882 10 171 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 171 210 3 3 57 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 171 210
  (Polychromatic418967fa.accept_12_8_3_6_1_909 8 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 171 210 (Polychromatic418967fa.accept_11_7_6_1_1_2182 7 171 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 171 210 3 2 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 171 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 171 210
  (Polychromatic418967fa.accept_12_4_3_6_1_879 4 171 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 3 171 210 3 1 57 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 2 171 210 (Polychromatic418967fa.accept_12_2_3_6_1_112 2 171 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 1 171 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 171 210))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 41 170 210 (Eq.refl Bool.true) (allA_succ_of_gcd 40 170 210 10 4 17 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 210
  (Polychromatic418967fa.accept_11_6_5_1_1_586 39 170 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 210 2 19 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 210 (accept_3_4 37 170 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 210 2 18 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 35 170 210 5 7 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 170 210 2 17 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 170 210 (Polychromatic418967fa.accept_9_6_8_3_1_183 33 170 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 170 210 2 16 85 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 170 210 (accept_3_4 31 170 210
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 170 210 10 3 17 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 170 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 29 170 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 170 210 2 14 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 170 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 27 170 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 170 210 2 13 85 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 25 170 210 5 5 34 42 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 170 210 2 12 85 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 170 210
  (Polychromatic418967fa.accept_9_5_8_3_1_437 23 170 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 170 210 2 11 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 170 210 (Polychromatic418967fa.accept_12_9_2_6_1_455 21 170 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 170 210 10 2 17 21 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 170 210 (accept_3_4 19 170 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 170 210 2 9 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 170 210 (Polychromatic418967fa.accept_11_6_5_1_1_586
  17 170 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 210 2 8 85 105
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 170 210 5 3 34 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 170 210 2 7 85
  105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 170 210
  (accept_3_4 13 170 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 170 210 2 6 85 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 170 210
  (Polychromatic418967fa.accept_9_2_8_3_1_181 11 170 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 170 210 10 1 17 21 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 170 210 (Polychromatic418967fa.accept_12_9_2_6_1_455 9 170 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 170 210 2 4 85 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 170 210 (accept_3_4 7 170 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170 210 2 3 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 170 210 5 1 34 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 4 170 210 2 2 85 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 170 210 (Polychromatic418967fa.accept_12_3_2_6_1_138 3
  170 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 210 2 1 85 105 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 210 (accept_3_4 1
  170 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 210)))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 42 169 210 (Eq.refl Bool.true) (allA_succ_of_accept 41 169 210 (accept_3_5 41 169 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 40 169 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 40 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 169 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 39 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 169 210 (accept_3_5 38 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  37 169 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 37 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 169 210 (Polychromatic418967fa.accept_20_16_9_10_1_6513 36 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 169 210 (accept_3_5 35 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 169 210 (Polychromatic418967fa.accept_19_15_17_1_1_8225 34 169
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 169 210
  (Polychromatic418967fa.accept_9_6_7_3_1_436 33 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 169 210 (accept_3_5 32 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 169 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 169 210 (Polychromatic418967fa.accept_11_8_4_1_1_1000 30 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 169 210 (accept_3_5 29 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 169 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 28 169 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 169 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 27 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 169 210 (accept_3_5 26 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 169 210 (Polychromatic418967fa.accept_20_5_9_10_1_12409 25 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 169 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 24 169 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 169 210 (accept_3_5 23 169 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 169 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 22 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 169 210
  (Polychromatic418967fa.accept_18_3_7_12_1_1196 21 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 169 210 (accept_3_5 20 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 169 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 169 210 (Polychromatic418967fa.accept_19_18_17_1_1_2789 18 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 169 210 (accept_3_5 17 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 169 210 (Polychromatic418967fa.accept_19_16_17_1_1_4011 16 169
  210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 169 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 15 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 169 210 (accept_3_5 14 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 169 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 13 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 169 210 (Polychromatic418967fa.accept_16_12_9_2_1_8989 12 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 169 210 (accept_3_5 11 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 169 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 10 169 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 169 210
  (Polychromatic418967fa.accept_17_9_16_6_1_4820 9 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 169 210 (accept_3_5 8 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  169 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 169 210 (Polychromatic418967fa.accept_9_6_7_3_1_436 6 169 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 169 210 (accept_3_5 5 169 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 169 210 (Polychromatic418967fa.accept_9_4_7_3_1_43 4 169 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 169 210
  (Polychromatic418967fa.accept_4_3_1_2_1_62 3 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 169 210 (accept_3_5 2 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  169 210 (Polychromatic418967fa.accept_9_1_7_3_1_41 1 169 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 169 210)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 168 210 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 168 210 42 1 4 5 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 168 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 41 168 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 168 210 2 20 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 168 210 3 13 56 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 168 210 2 19 84 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 37 168 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 168 210 6 6 28 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 35 168 210 7 5 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 34 168 210 2 17 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 33 168 210 3 11 56 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 32 168 210 2 16 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 168 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 31 168 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 168 210 6 5 28 35 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 168 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 29 168 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 168 210 14 2 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 27 168 210 3 9 56 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 26 168 210 2 13 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 168 210 (Polychromatic418967fa.accept_9_7_6_3_1_456 25 168 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 168 210 6 4 28 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 168 210
  (Polychromatic418967fa.accept_9_5_6_3_1_40 23 168 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 168 210 2 11 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 168 210 21 1 8 10 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 168 210 2 10 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 168 210 (Polychromatic418967fa.accept_9_1_6_3_1_177 19 168 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 210 6 3 28 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 210
  (Polychromatic418967fa.accept_9_8_6_3_1_457 17 168 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 210 2 8 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 168 210 3 5 56 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 168 210 14 1 12 15 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 210 (Polychromatic418967fa.accept_9_4_6_3_1_179 13 168 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 210 6 2 28 35 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 210
  (Polychromatic418967fa.accept_9_2_6_3_1_178 11 168 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 168 210 2 5 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 168 210 3 3 56 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 168 210 2 4 84 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 7 168 210 7 1 24 30 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 6 168 210 6 1 28 35 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 168 210 (Polychromatic418967fa.accept_9_5_6_3_1_40 5 168 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 168 210 2 2 84 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 168 210 3 1 56 70 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 168 210 2 1 84 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 210
  (Polychromatic418967fa.accept_9_1_6_3_1_177 1 168 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 168 210))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 167 210 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 167 210 (accept_3_4 43 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 42 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 210 (accept_3_4 40 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 210 (Polychromatic418967fa.accept_20_19_7_10_1_12343 39 167 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 38 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 167 210 (accept_3_4 37 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 167 210 (Polychromatic418967fa.accept_11_3_2_1_1_994 36 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 210 (Polychromatic418967fa.accept_9_8_5_3_1_777 35 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 210 (accept_3_4 34 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 167 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 210
  (Polychromatic418967fa.accept_11_10_2_1_1_1036 32 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 210 (accept_3_4 31 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 210 (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 210 (accept_3_4 28 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 210 (Polychromatic418967fa.accept_16_11_7_2_1_4185 27 167 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 26 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 210 (accept_3_4 25 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 24 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 210 (Polychromatic418967fa.accept_13_10_11_2_1_3862 23 167 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 210 (accept_3_4 22 167 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 20 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 210 (accept_3_4 19 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 210 (Polychromatic418967fa.accept_20_18_7_10_1_3596 18 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 210 (accept_3_4 16 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 15 167 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 210
  (Polychromatic418967fa.accept_11_3_2_1_1_994 14 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 210 (accept_3_4 13 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 210 (Polychromatic418967fa.accept_16_12_7_2_1_4159 12 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 210 (Polychromatic418967fa.accept_9_2_5_3_1_37 11 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 210 (accept_3_4 10 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 167 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 210
  (Polychromatic418967fa.accept_9_8_5_3_1_777 8 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 210 (accept_3_4 7 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 210 (Polychromatic418967fa.accept_9_6_5_3_1_205 6 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 210 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 210 (accept_3_4 4 167 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 210 (Polychromatic418967fa.accept_11_3_2_1_1_994 3 167 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 210
  (Polychromatic418967fa.accept_9_2_5_3_1_37 2 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 210 (accept_3_4 1 167 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  210)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 166 210 (Eq.refl Bool.true) (allA_succ_of_gcd 44 166
  210 2 22 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  43 166 210 (Polychromatic418967fa.accept_9_7_4_3_1_204 43 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 166 210 2 21 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 166 210 (accept_3_5 41 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 166 210 2 20 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 166 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 39 166 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 166 210 2 19 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 166 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 37 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 166 210 2 18 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 166 210 (accept_3_5 35 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 166 210 2 17 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 166 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 33 166 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 166 210 2 16 83 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 166 210
  (Polychromatic418967fa.accept_13_5_10_2_1_856 31 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 166 210 2 15 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 166 210 (accept_3_5 29 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 166 210 2 14 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 166 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 27 166 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 166 210 2 13 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 166 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 25 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 166 210 2 12 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 166 210 (accept_3_5 23 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 166 210 2 11 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 166 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 21 166 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 166 210 2 10 83 105 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 166 210
  (Polychromatic418967fa.accept_9_1_4_3_1_201 19 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 166 210 2 9 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 166 210 (accept_3_5 17 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 166 210 2 8 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 166 210 (Polychromatic418967fa.accept_9_6_4_3_1_203 15 166 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 166 210 2 7 83 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 166 210
  (Polychromatic418967fa.accept_19_13_14_1_1_3996 13 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 166 210 2 6 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 166 210 (accept_3_5 11 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 166 210 2 5 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 166 210 (Polychromatic418967fa.accept_12_9_10_6_1_872 9 166 210 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 166 210 2 4 83 105 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 166 210
  (Polychromatic418967fa.accept_9_7_4_3_1_204 7 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 166 210 2 3 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 166 210 (accept_3_5 5 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 166
  210 2 2 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3
  166 210 (Polychromatic418967fa.accept_12_3_10_6_1_442 3 166 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 166 210 2 1 83 105 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 166 210 (Polychromatic418967fa.accept_9_1_4_3_1_201 1 166 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 166 210)))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 46 165 210 (Eq.refl Bool.true) (allA_succ_of_gcd 45 165 210 15 3 11 14 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 165 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 44 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 165 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 43 165 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 165 210 3 14 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 165 210 (Polychromatic418967fa.accept_20_1_5_10_1_3534
  41 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 165 210 5 8 33 42
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 165 210 3 13 55
  70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 165 210
  (Polychromatic418967fa.accept_12_2_9_6_1_439 38 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 165 210 (Polychromatic418967fa.accept_13_11_9_2_1_2969 37 165 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 165 210 3 12 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 35 165 210 5 7 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 34 165 210 (Polychromatic418967fa.accept_12_10_9_6_1_1445
  34 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 165 210 3 11 55 70
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 165 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 32 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 165 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 31 165 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 165 210 15 2 11 14 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 165 210 (Polychromatic418967fa.accept_13_3_9_2_1_1486
  29 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 165 210
  (Polychromatic418967fa.accept_12_4_9_6_1_440 28 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 165 210 3 9 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 165 210 (Polychromatic418967fa.accept_12_2_9_6_1_439 26 165 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 25 165 210 5 5 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 24 165 210 3 8 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 165 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 23
  165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 165 210
  (Polychromatic418967fa.accept_12_10_9_6_1_1445 22 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 21 165 210 3 7 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 20 165 210 5 4 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 165 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 19 165 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 165 210 3 6 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 165 210
  (Polychromatic418967fa.accept_20_17_5_10_1_3591 17 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 16 165 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 16 165 210 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 165 210 15 1 11 14 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 165 210
  (Polychromatic418967fa.accept_12_2_9_6_1_439 14 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 165 210 (Polychromatic418967fa.accept_16_13_5_2_1_2131 13 165 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 165 210 3 4 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 165 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 11
  165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 165 210 5 2 33 42 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 165 210 3 3 55 70 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 165 210
  (Polychromatic418967fa.accept_12_8_9_6_1_127 8 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 165 210 (Polychromatic418967fa.accept_4_3_1_2_1_62 7 165 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 165 210 3 2 55 70 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 5 165 210 5 1 33 42 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 4 165 210 (Polychromatic418967fa.accept_12_4_9_6_1_440 4 165 210
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 165 210 3 1 55 70 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 165 210
  (Polychromatic418967fa.accept_12_2_9_6_1_439 2 165 210 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 165 210 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 165 210 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 165 210))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_210_segment_001)))))))))))))))))))))))))))))))))))))))))))))


