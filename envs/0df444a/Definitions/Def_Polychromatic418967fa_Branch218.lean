-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch218
-- name    : Polychromatic418967fa_Branch218
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:24:40.205941+00:00
-- url     : https://prove2.me/theorems/a6ac8df8-907b-4bde-8976-081e2920406a
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch218_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_218 : allB 218 218 :=
  allB_succ' 2 217 218 (Eq.refl Bool.true) (allA_of_3_0 2 217 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 3
  216 218 (Eq.refl Bool.true) (allA_succ_of_gcd 2 216 218 2 1 108 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 216 218 (accept_3_2 1 216 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 216 218))) (allB_succ' 4 215 218 (Eq.refl Bool.true) (allA_succ_of_accept 3 215 218
  (Polychromatic418967fa.accept_6_3_5_2_1_12 3 215 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 215 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 215 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 215 218 (accept_3_2 1 215 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 215 218)))) (allB_succ' 5 214 218 (Eq.refl Bool.true) (allA_of_3_0 5 214 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 6 213 218 (Eq.refl Bool.true) (allA_succ_of_accept 5 213 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 213 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 213 218 (accept_3_2 4 213 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  213 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 213 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 213 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 213 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 213 218 (accept_3_2 1 213 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 213 218)))))) (allB_succ' 7 212 218 (Eq.refl Bool.true) (allA_succ_of_gcd 6 212 218 2 3
  106 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 212 218
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 212 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 212 218 2 2 106 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 212 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 212 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 212 218 2 1 106 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 212 218 (accept_3_2 1 212 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 212 218))))))) (allB_succ' 8 211 218 (Eq.refl Bool.true) (allA_of_3_0 8 211
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 9 210 218 (Eq.refl Bool.true) (allA_succ_of_gcd 8 210 218 2 4
  105 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 210 218
  (accept_3_2 7 210 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 210 218 2 3 105 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 210 218
  (Polychromatic418967fa.accept_9_5_3_2_1_171 5 210 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 210 218 2 2 105 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 210 218 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 210 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 210 218 2 1 105 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 210 218 (accept_3_2 1 210 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 210 218))))))))) (allB_succ' 10 209 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 9 209 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 209 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 209 218 (Polychromatic418967fa.accept_12_8_5_2_1_746 8 209 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 209 218 (accept_3_2 7 209 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 209 218 (Polychromatic418967fa.accept_15_6_14_8_1_245
  6 209 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 209 218
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 209 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 209 218 (accept_3_2 4 209 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  209 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 209 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 209 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 209 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 209 218 (accept_3_2 1 209 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 209 218)))))))))) (allB_succ' 11 208 218 (Eq.refl Bool.true) (allA_of_3_0 11 208 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 12 207 218 (Eq.refl Bool.true) (allA_succ_of_accept 11 207 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 207 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 207 218 (accept_3_2 10 207 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  207 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 207 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 207 218 (Polychromatic418967fa.accept_13_8_12_10_1_4414 8 207 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 207 218 (accept_3_2 7 207 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 207 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 207 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 207 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 207 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 207 218 (accept_3_2 4 207 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  207 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 207 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 207 218 (Polychromatic418967fa.accept_13_2_12_10_1_2649 2 207 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 207 218 (accept_3_2 1 207 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 207 218)))))))))))) (allB_succ' 13 206 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 12 206 218 2 6 103 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 206 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 206 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 206 218 2 5 103 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 206 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 206 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 206 218 2 4 103 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 206 218 (accept_3_2 7 206 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 206 218 2 3 103 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 206 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 206 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 206 218 2 2 103 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 206 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 3 206 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 206 218 2 1 103 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 206 218 (accept_3_2 1 206 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 206
  218))))))))))))) (allB_succ' 14 205 218 (Eq.refl Bool.true) (allA_of_3_0 14 205 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 15 204 218 (Eq.refl Bool.true) (allA_succ_of_gcd 14 204 218 2 7 102 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 204 218 (accept_3_2 13 204 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 204 218 2 6 102 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 204 218
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 11 204 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 204 218 2 5 102 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 204 218 (Polychromatic418967fa.accept_10_9_4_8_1_741 9 204 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 204 218 2 4 102 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 204 218 (accept_3_2 7 204 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 204 218 2 3 102 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 204 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 5 204 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 204 218 2 2 102 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 204 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 204 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 204 218 2 1 102 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 204 218 (accept_3_2 1 204 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 204 218))))))))))))))) (allB_succ' 16 203 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 15 203 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 203 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 203 218 (Polychromatic418967fa.accept_25_14_3_18_1_12971 14
  203 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 203 218 (accept_3_2 13
  203 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 203 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 203 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 203 218 (Polychromatic418967fa.accept_10_1_3_8_1_136 11 203 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 203 218 (accept_3_2 10 203 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 203 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 203 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 203 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 8
  203 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 203 218 (accept_3_2 7 203
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 203 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 203 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 203 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 203 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 203 218 (accept_3_2 4 203 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 203 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 203 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 203 218 (Polychromatic418967fa.accept_13_2_8_10_1_1902
  2 203 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 203 218 (accept_3_2 1
  203 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 203 218)))))))))))))))) (allB_succ' 17 202 218 (Eq.refl
  Bool.true) (allA_of_3_0 17 202 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 18 201 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 201 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 201 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 201 218 (accept_3_2 16 201 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 201 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 201 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 201 218 (Polychromatic418967fa.accept_9_5_3_2_1_171
  14 201 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 201 218 (accept_3_2 13
  201 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 201 218
  (Polychromatic418967fa.accept_13_12_6_10_1_667 12 201 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 201 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 201 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 201 218 (accept_3_2 10 201 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 201 218 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 201 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 201 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 8
  201 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 201 218 (accept_3_2 7 201
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 201 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 201 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 201 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 201 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 201 218 (accept_3_2 4 201 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 201 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 201 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 201 218 (Polychromatic418967fa.accept_13_2_6_10_1_2703
  2 201 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 201 218 (accept_3_2 1
  201 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 201 218)))))))))))))))))) (allB_succ' 19 200 218 (Eq.refl
  Bool.true) (allA_succ_of_gcd 18 200 218 2 9 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 200 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 200 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 200 218 2 8 100 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 200 218
  (Polychromatic418967fa.accept_11_4_2_9_1_496 15 200 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 200 218 2 7 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 200 218 (accept_3_2 13 200 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 200 218 2 6 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 200 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 200 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 200 218 2 5 100 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 200 218
  (Polychromatic418967fa.accept_27_9_11_2_1_414 9 200 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 200 218 2 4 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 200 218 (accept_3_2 7 200 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 200 218 2 3 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 200 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 200 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 200 218 2 2 100 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 200 218
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 200 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 200 218 2 1 100 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 200 218 (accept_3_2 1 200 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 200
  218))))))))))))))))))) (allB_succ' 20 199 218 (Eq.refl Bool.true) (allA_of_3_0 20 199 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allB_succ' 21 198 218 (Eq.refl Bool.true) (allA_succ_of_gcd 20 198 218 2 10 99 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 198 218 (accept_3_2 19 198 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 198 218 2 9 99 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 198 218
  (Polychromatic418967fa.accept_7_3_2_1_1_225 17 198 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 198 218 2 8 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 198 218 (Polychromatic418967fa.accept_12_3_6_2_1_747 15 198 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 198 218 2 7 99 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 198 218 (accept_3_2 13 198 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 198 218 2 6 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 198 218
  (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 198 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 198 218 2 5 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 198 218 (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 198 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 198 218 2 4 99 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 198 218 (accept_3_2 7 198 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 198 218 2 3 99 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 198 218
  (Polychromatic418967fa.accept_15_5_3_8_1_748 5 198 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 198 218 2 2 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 198 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 198 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 198 218 2 1 99 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 198 218 (accept_3_2 1 198 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 198 218))))))))))))))))))))) (allB_succ' 22 197 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 21 197 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 197 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 197 218 (Polychromatic418967fa.accept_12_8_5_2_1_746 20 197
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 197 218 (accept_3_2 19 197
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 197 218
  (Polychromatic418967fa.accept_13_5_2_10_1_248 18 197 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 197 218 (Polychromatic418967fa.accept_19_17_7_9_1_3324 17 197 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 197 218 (accept_3_2 16 197 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 197 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 197 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 197 218 (Polychromatic418967fa.accept_9_5_8_2_1_409
  14 197 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 197 218 (accept_3_2 13
  197 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 197 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 12 197 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 197 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 197 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 197 218 (accept_3_2 10 197 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 197 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 197 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 197 218 (Polychromatic418967fa.accept_11_8_10_9_1_1401
  8 197 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 197 218 (accept_3_2 7
  197 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 197 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 6 197 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 197 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 197 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 197 218 (accept_3_2 4 197 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 197 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 197 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 197 218 (Polychromatic418967fa.accept_14_2_1_8_1_650 2
  197 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 197 218 (accept_3_2 1 197
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 197 218)))))))))))))))))))))) (allB_succ' 23 196 218 (Eq.refl
  Bool.true) (allA_of_3_0 23 196 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 24 195 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 23 195 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 195 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 195 218 (accept_3_2 22 195 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 195 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 195 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 195 218
  (Polychromatic418967fa.accept_19_1_5_9_1_10341 20 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 195 218 (accept_3_2 19 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 195 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 195 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 195 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 195 218 (accept_3_2 16 195 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 195 218 (Polychromatic418967fa.accept_19_15_5_9_1_3299 15 195 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 195 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 195 218 (accept_3_2 13 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 195 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 195 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 195 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 195 218 (accept_3_2 10 195 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 195 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 195 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 195 218
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 195 218 (accept_3_2 7 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  195 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 195 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 195 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 195 218 (accept_3_2 4 195 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 195 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 195 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 195 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 195 218 (accept_3_2 1 195 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 195
  218)))))))))))))))))))))))) (allB_succ' 25 194 218 (Eq.refl Bool.true) (allA_succ_of_gcd 24 194 218 2 12 97 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 194 218
  (Polychromatic418967fa.accept_17_6_7_14_1_6704 23 194 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 194 218 2 11 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 194 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 194 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 194 218 2 10 97 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 194 218 (accept_3_2 19 194 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 194 218 2 9 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 194 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  194 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 194 218 2 8 97 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 194 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 194 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 194 218 2 7 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 194 218 (accept_3_2 13 194 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 194 218 2 6 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 194 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 194 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 194 218 2 5 97 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 194 218
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 194 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 194 218 2 4 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 194 218 (accept_3_2 7 194 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 194
  218 2 3 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  194 218 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 194 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 194 218 2 2 97 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 194 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 194 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 194 218 2 1 97 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 194 218 (accept_3_2 1 194 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 194 218))))))))))))))))))))))))) (allB_succ' 26 193 218 (Eq.refl
  Bool.true) (allA_of_3_0 26 193 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 27 192 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 192 218 2 13 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 192 218 (accept_3_2 25 192 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 192 218 2 12 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 192 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 192 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 192 218 2 11 96 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 192 218
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 21 192 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 192 218 2 10 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 192 218 (accept_3_2 19 192 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 192 218 2 9 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 192 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 192 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 192 218 2 8 96 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 192 218
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 192 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 192 218 2 7 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 192 218 (accept_3_2 13 192 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 192 218 2 6 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 192 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 192 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 192 218 2 5 96 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 192 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 192 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 192 218 2 4 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 192 218 (accept_3_2 7 192 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 192
  218 2 3 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  192 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 192 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 192 218 2 2 96 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 192 218 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 192 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 192 218 2 1 96 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 192 218 (accept_3_2 1 192 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 192 218))))))))))))))))))))))))))) (allB_succ' 28 191 218 (Eq.refl
  Bool.true) (allA_succ_of_accept 27 191 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 191 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 191 218
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 26 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 191 218 (accept_3_2 25 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 191 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 191 218 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 191 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 191 218 (accept_3_2 22 191 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 191 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 191 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 191 218
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 191 218 (accept_3_2 19 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 191 218 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 191 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 191 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 191 218 (accept_3_2 16 191 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 191 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 191 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 191 218
  (Polychromatic418967fa.accept_13_1_9_10_1_625 14 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 191 218 (accept_3_2 13 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 191 218 (Polychromatic418967fa.accept_13_12_9_10_1_1223 12 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 191 218 (Polychromatic418967fa.accept_16_11_15_10_1_3515 11 191 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 191 218 (accept_3_2 10 191 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 191 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 191 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 191 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 191 218 (accept_3_2 7 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  191 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 191 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 191 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 191 218 (accept_3_2 4 191 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 191 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 191 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 191 218
  (Polychromatic418967fa.accept_11_2_4_9_1_484 2 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 191 218 (accept_3_2 1 191 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 191
  218)))))))))))))))))))))))))))) (allB_succ' 29 190 218 (Eq.refl Bool.true) (allA_of_3_0 29 190 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allB_succ' 30 189 218 (Eq.refl Bool.true) (allA_succ_of_accept 29 189 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 189 218 (accept_3_2 28 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 189 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 189 218 (Polychromatic418967fa.accept_11_4_2_9_1_496 26 189 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 189 218 (accept_3_2 25 189 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 189 218 (Polychromatic418967fa.accept_10_4_9_8_1_125 24 189
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 189 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 189 218 (accept_3_2 22 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 189 218 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 189 218 (Polychromatic418967fa.accept_14_6_7_8_1_624 20 189 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 189 218 (accept_3_2 19 189 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 189 218 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 189
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 189 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 189 218 (accept_3_2 16 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 189 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 189 218 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 189 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 189 218 (accept_3_2 13 189 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 189 218 (Polychromatic418967fa.accept_13_12_7_10_1_2662 12 189
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 189 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 189 218 (accept_3_2 10 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  189 218 (Polychromatic418967fa.accept_24_9_21_2_1_12970 9 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 189 218 (Polychromatic418967fa.accept_13_8_7_10_1_4362 8 189 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 189 218 (accept_3_2 7 189 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 189 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 189 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 189 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 189 218 (accept_3_2 4 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  189 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 189 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 189 218 (Polychromatic418967fa.accept_15_2_9_8_1_736 2 189 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 189 218 (accept_3_2 1 189 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 189 218)))))))))))))))))))))))))))))) (allB_succ' 31 188 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 30 188 218 2 15 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 188 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 188 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 188 218 2 14 94 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 188 218
  (Polychromatic418967fa.accept_16_11_12_10_1_3641 27 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 188 218 2 13 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 188 218 (accept_3_2 25 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 188 218 2 12 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 188 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 188 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 188 218 2 11 94 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 188 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 188 218 2 10 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 188 218 (accept_3_2 19 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 188 218 2 9 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 188 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 188 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 188 218 2 8 94 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 188 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 188 218 2 7 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 188 218 (accept_3_2 13 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 188 218 2 6 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 188 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 188 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 188 218 2 5 94 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 188 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 188 218 2 4 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 188 218 (accept_3_2 7 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 188
  218 2 3 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  188 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 188 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 188 218 2 2 94 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 188 218 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 188 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 188 218 2 1 94 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 188 218 (accept_3_2 1 188 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 188 218))))))))))))))))))))))))))))))) (allB_succ' 32 187 218
  (Eq.refl Bool.true) (allA_of_3_0 32 187 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 33 186 218 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 186 218 2 16 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 186 218 (accept_3_2 31 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 218 2 15 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 218 (Polychromatic418967fa.accept_15_14_6_8_1_1410 29 186 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 218 2 14 93 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 218 2 13 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 218 (accept_3_2 25 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 218 2 12 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 186 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 218 2 11 93 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 218
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 218 2 10 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 218 (accept_3_2 19 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 218 2 9 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 186 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 218 2 8 93 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 218 2 7 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 218 (accept_3_2 13 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 218 2 6 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 218 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 186 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 218 2 5 93 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 218 2 4 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 218 (accept_3_2 7 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  218 2 3 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 186 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 218 2 2 93 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 186 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 218 2 1 93 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 218 (accept_3_2 1 186 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186 218))))))))))))))))))))))))))))))))) (allB_succ' 34 185 218
  (Eq.refl Bool.true) (allA_succ_of_accept 33 185 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 218
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 218 (accept_3_2 31 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 218 (Polychromatic418967fa.accept_15_14_5_8_1_3175 29 185 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 218 (accept_3_2 28 185 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 185 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 218
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 218 (accept_3_2 25 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 218 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 185 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 218 (accept_3_2 22 185 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 218 (accept_3_2 19 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 185 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 218 (accept_3_2 16 185 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 185 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 218
  (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 218 (accept_3_2 13 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 185 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 218 (accept_3_2 10 185 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 218
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 218 (accept_3_2 7 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 218 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 185 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 218 (accept_3_2 4 185 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 185 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 218 (accept_3_2 1 185 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  218)))))))))))))))))))))))))))))))))) (allB_succ' 35 184 218 (Eq.refl Bool.true) (allA_of_3_0 35 184 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allB_succ' 36 183 218 (Eq.refl Bool.true) (allA_succ_of_accept 35 183 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 183 218 (accept_3_2 34 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 183 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 183 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 218 (accept_3_2 31 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 183 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 183 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 183 218 (accept_3_2 28 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 183 218 (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 183 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 218 (accept_3_2 25 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 183 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 183 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 183 218 (accept_3_2 22 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 183 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 183 218 (Polychromatic418967fa.accept_15_5_3_8_1_748 20 183 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 218 (accept_3_2 19 183 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 183 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 183
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 218 (accept_3_2 16 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 218 (accept_3_2 13 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 218 (Polychromatic418967fa.accept_15_12_3_8_1_5245 12 183 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 218 (accept_3_2 10 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 218 (accept_3_2 7 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 183 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 218 (accept_3_2 4 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 218 (Polychromatic418967fa.accept_16_3_7_10_1_3503 3 183 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 218 (Polychromatic418967fa.accept_11_2_7_9_1_890 2 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 218 (accept_3_2 1 183 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183 218)))))))))))))))))))))))))))))))))))) (allB_succ' 37 182 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 182 218 2 18 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 218 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 182 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 218 2 17 91 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 218
  (Polychromatic418967fa.accept_19_14_11_9_1_3330 33 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 182 218 2 16 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 182 218 (accept_3_2 31 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 218 2 15 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 218 (Polychromatic418967fa.accept_31_29_27_1_1_12969 29 182 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 218 2 14 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 218
  (Polychromatic418967fa.accept_19_8_11_9_1_8827 27 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 218 2 13 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 218 (accept_3_2 25 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 218 2 12 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 218 (Polychromatic418967fa.accept_20_3_2_18_1_11577 23 182 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 218 2 11 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 218
  (Polychromatic418967fa.accept_15_6_2_8_1_2223 21 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 182 218 2 10 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 182 218 (accept_3_2 19 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 218 2 9 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 218 (Polychromatic418967fa.accept_19_17_11_9_1_2141 17 182 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 218 2 8 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 218
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 182 218 2 7 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 182 218 (accept_3_2 13 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 218 2 6 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 218 (Polychromatic418967fa.accept_17_11_12_14_1_5431 11 182 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 218 2 5 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 218
  (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 218 2 4 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 218 (accept_3_2 7 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  218 2 3 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 218 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 182 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 218 2 2 91 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 218 (Polychromatic418967fa.accept_11_3_6_9_1_1378 3 182 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 218 2 1 91 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 218 (accept_3_2 1 182 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182 218))))))))))))))))))))))))))))))))))))) (allB_succ' 38 181 218
  (Eq.refl Bool.true) (allA_of_3_0 38 181 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 39 180 218 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 180 218 2 19 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 180 218 (accept_3_2 37 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 218 2 18 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 180 218 (Polychromatic418967fa.accept_11_2_4_9_1_484 35 180 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 218 2 17 90 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 218
  (Polychromatic418967fa.accept_27_6_18_2_1_12968 33 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 180 218 2 16 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 180 218 (accept_3_2 31 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 218 2 15 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 218 (Polychromatic418967fa.accept_13_3_11_10_1_2647 29 180 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 218 2 14 90 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 180 218 2 13 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 180 218 (accept_3_2 25 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 218 2 12 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 180 218 (Polychromatic418967fa.accept_25_23_5_18_1_12967 23 180 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 218 2 11 90 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 218
  (Polychromatic418967fa.accept_13_8_11_10_1_636 21 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 180 218 2 10 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 180 218 (accept_3_2 19 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 218 2 9 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 180 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 218 2 8 90 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 180 218
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 180 218 2 7 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 180 218 (accept_3_2 13 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 218 2 6 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 180 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 180 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 218 2 5 90 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 218
  (Polychromatic418967fa.accept_21_9_12_8_1_5255 9 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 180 218 2 4 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 180 218 (accept_3_2 7 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 180
  218 2 3 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  180 218 (Polychromatic418967fa.accept_17_5_10_14_1_2083 5 180 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 180 218 2 2 90 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 180 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 180 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 218 2 1 90 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 218 (accept_3_2 1 180 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180 218))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 179
  218 (Eq.refl Bool.true) (allA_succ_of_accept 39 179 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 179 218
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 179 218 (accept_3_2 37 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 179 218 (Polychromatic418967fa.accept_15_6_14_8_1_245 36 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 179 218 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 179 218 (accept_3_2 34 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 179 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 179 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 218
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 179 218 (accept_3_2 31 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 179 218 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 179 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 179 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 179 218 (accept_3_2 28 179 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 179 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 218
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 179 218 (accept_3_2 25 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 179 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 179 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 179 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 179 218 (accept_3_2 22 179 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 179 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 179 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 179 218 (accept_3_2 19 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 179 218 (Polychromatic418967fa.accept_14_4_11_8_1_2034 18 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 179 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 179 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 179 218 (accept_3_2 16 179 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 179 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 179 218
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 179 218 (accept_3_2 13 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 179 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 179 218 (Polychromatic418967fa.accept_10_1_9_8_1_123 11 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 179 218 (accept_3_2 10 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 179 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 179 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 179 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 179 218 (accept_3_2 7 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  179 218 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 179 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 179 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 179 218 (accept_3_2 4 179 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 179 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 179 218
  (Polychromatic418967fa.accept_22_2_3_20_1_4812 2 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 179 218 (accept_3_2 1 179 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 179
  218)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 178 218 (Eq.refl Bool.true) (allA_of_3_0 41 178 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 42 177 218 (Eq.refl Bool.true) (allA_succ_of_accept 41 177 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 177 218 (accept_3_2 40 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 177 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 177 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 38 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 177 218 (accept_3_2 37 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 177 218 (Polychromatic418967fa.accept_19_17_6_9_1_8856 36 177 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 177 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 177 218 (accept_3_2 34 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 177 218 (Polychromatic418967fa.accept_13_7_8_10_1_2663 33 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 177 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 177 218 (accept_3_2 31 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 177 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 177 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 177 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 177 218 (accept_3_2 28 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 177 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 177 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 177 218 (accept_3_2 25 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 177 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 177 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 177 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 177 218 (accept_3_2 22 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 177 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 177 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 20 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 177 218 (accept_3_2 19 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 177 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 177 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 177 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 177 218 (accept_3_2 16 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 177 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 177 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 177 218 (accept_3_2 13 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 177 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 177 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 177 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 177 218 (accept_3_2 10 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  177 218 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 177 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 177 218 (accept_3_2 7 177 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 177 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 177 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 177 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 177 218 (accept_3_2 4 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  177 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 177 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 177 218 (Polychromatic418967fa.accept_13_2_8_10_1_1902 2 177 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 177 218 (accept_3_2 1 177 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 177 218)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 176 218
  (Eq.refl Bool.true) (allA_succ_of_gcd 42 176 218 2 21 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 176 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 176 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 218 2 20 88 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 218 2 19 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 218 (accept_3_2 37 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 218 2 18 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 176 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 176 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 218 2 17 88 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 176 218 2 16 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 176 218 (accept_3_2 31 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 176 218 2 15 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 176 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 176 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 176 218 2 14 88 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 176 218
  (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 176 218 2 13 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 176 218 (accept_3_2 25 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 176 218 2 12 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 176 218 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 176 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 176 218 2 11 88 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 176 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 176 218 2 10 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 176 218 (accept_3_2 19 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 176 218 2 9 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 176 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 176 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 218 2 8 88 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 218 2 7 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 218 (accept_3_2 13 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 218 2 6 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 176 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 176 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 218 2 5 88 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 218
  (Polychromatic418967fa.accept_28_9_8_22_1_12966 9 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 176 218 2 4 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 176 218 (accept_3_2 7 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176
  218 2 3 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  176 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 176 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 176 218 2 2 88 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 176 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 176 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 218 2 1 88 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 218 (accept_3_2 1 176 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 176 218))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44
  175 218 (Eq.refl Bool.true) (allA_of_3_0 44 175 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 45 174 218
  (Eq.refl Bool.true) (allA_succ_of_gcd 44 174 218 2 22 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 174 218 (accept_3_2 43 174 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 42 174 218 2 21 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 41 174 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 174 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 218 2 20 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 218
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 218 2 19 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 218 (accept_3_2 37 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 218 2 18 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 174 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 218 2 17 87 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 218
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 218 2 16 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 218 (accept_3_2 31 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 218 2 15 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 218 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 174 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 218 2 14 87 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 218 2 13 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 218 (accept_3_2 25 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 218 2 12 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 174 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 218 2 11 87 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 218 2 10 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 218 (accept_3_2 19 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 218 2 9 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 174 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 218 2 8 87 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 218
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 218 2 7 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 218 (accept_3_2 13 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 218 2 6 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 218 (Polychromatic418967fa.accept_19_11_3_9_1_8882 11 174 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 218 2 5 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 218 2 4 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 218 (accept_3_2 7 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  218 2 3 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 174 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 218 2 2 87 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 218 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 174 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 218 2 1 87 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 218 (accept_3_2 1 174 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174 218))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  173 218 (Eq.refl Bool.true) (allA_succ_of_accept 45 173 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 218 (accept_3_2 43 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 218 (Polychromatic418967fa.accept_19_4_2_9_1_4584 42 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 218 (accept_3_2 40 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 173 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 218
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 218 (accept_3_2 37 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 218 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 218 (accept_3_2 34 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 218
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 218 (accept_3_2 31 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 218 (Polychromatic418967fa.accept_16_14_13_10_1_2624 30 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 218 (Polychromatic418967fa.accept_25_4_23_18_1_12935 29 173 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 218 (accept_3_2 28 173 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 218
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 218 (accept_3_2 25 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 218 (accept_3_2 22 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 218 (accept_3_2 19 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 218 (accept_3_2 16 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 173 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 218
  (Polychromatic418967fa.accept_13_1_4_10_1_622 14 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 218 (accept_3_2 13 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 218 (Polychromatic418967fa.accept_16_12_13_10_1_2637 12 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 11 173 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 173 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 218 (accept_3_2 10 173 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 218 (accept_3_2 7 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 218 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 218 (accept_3_2 4 173 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 173 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 218
  (Polychromatic418967fa.accept_17_2_3_14_1_8043 2 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 218 (accept_3_2 1 173 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  218)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 172 218 (Eq.refl Bool.true) (allA_of_3_0 47 172 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 48 171 218 (Eq.refl Bool.true) (allA_succ_of_accept 47 171 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 218 (accept_3_2 46 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 44 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 218 (accept_3_2 43 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 41 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 218 (accept_3_2 40 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 218 (Polychromatic418967fa.accept_13_12_2_10_1_2698 38 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 218 (accept_3_2 37 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 218 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 171
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 218 (accept_3_2 34 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 218 (accept_3_2 31 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 218 (accept_3_2 28 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 218 (Polychromatic418967fa.accept_17_10_1_14_1_489 27 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 26 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 218 (accept_3_2 25 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 218 (Polychromatic418967fa.accept_13_11_2_10_1_4399 24 171 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 218 (accept_3_2 22 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 218 (Polychromatic418967fa.accept_23_20_10_11_1_12965 20 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 218 (accept_3_2 19 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 171 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 218 (accept_3_2 16 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 218 (Polychromatic418967fa.accept_16_15_11_10_1_3639 15 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 218 (Polychromatic418967fa.accept_11_3_6_9_1_1378 14 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 218 (accept_3_2 13 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 171 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 218 (accept_3_2 10 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 218 (Polychromatic418967fa.accept_13_8_2_10_1_652 8 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 218 (accept_3_2 7 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 6 171 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 218 (accept_3_2 4 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 218 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 171 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 2 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 218 (accept_3_2 1 171 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171 218)))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 49 170 218 (Eq.refl
  Bool.true) (allA_succ_of_gcd 48 170 218 2 24 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 47 170 218 (Polychromatic418967fa.accept_20_7_10_18_1_10001 47 170 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 170 218 2 23 85 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 170 218
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 170 218 2 22 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 170 218 (accept_3_2 43 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 170 218 2 21 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 170 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 170 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 218 2 20 85 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 218 2 19 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 218 (accept_3_2 37 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 218 2 18 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 218 (Polychromatic418967fa.accept_13_9_1_10_1_647 35 170 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 218 2 17 85 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 170 218 2 16 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 170 218 (accept_3_2 31 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 170 218 2 15 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 170 218 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 170 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 170 218 2 14 85 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 170 218
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 170 218 2 13 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 170 218 (accept_3_2 25 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 170 218 2 12 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 170 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 170 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 170 218 2 11 85 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 170 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 170 218 2 10 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 170 218 (accept_3_2 19 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 170 218 2 9 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 170 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 170 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 170 218 2 8 85 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 218 2 7 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 218 (accept_3_2 13 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 218 2 6 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 218 (Polychromatic418967fa.accept_13_11_1_10_1_648 11 170 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 218 2 5 85 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 218
  (Polychromatic418967fa.accept_13_9_1_10_1_647 9 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 218 2 4 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 218 (accept_3_2 7 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  218 2 3 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 170 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 218 2 2 85 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 170 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 218 2 1 85 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 218 (accept_3_2 1 170 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170 218)))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 50 169 218 (Eq.refl Bool.true) (allA_of_3_0 50 169 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 51 168 218 (Eq.refl Bool.true) (allA_succ_of_gcd 50 168 218 2 25 84 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 168 218 (accept_3_2 49 168 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 168 218 2 24 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 168 218
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 47 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 46 168 218 2 23 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 45 168 218 (Polychromatic418967fa.accept_13_6_12_10_1_690 45 168 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 218 2 22 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 218 (accept_3_2 43 168 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 218 2 21 84 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 218 2 20 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 39 168 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 168 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 218 2 19 84 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 218 (accept_3_2 37 168 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 218 2 18 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 35
  168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 218 2 17 84 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 218
  (Polychromatic418967fa.accept_13_7_12_10_1_640 33 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 168 218 2 16 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 168 218 (accept_3_2 31 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 218 2 15 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 218 (Polychromatic418967fa.accept_17_12_15_14_1_6746 29 168 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 218 2 14 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 218
  (Polychromatic418967fa.accept_15_12_3_8_1_5245 27 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 168 218 2 13 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 218 (accept_3_2 25 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 218 2 12 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 168 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 168 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 218 2 11 84 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 218
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 168 218 2 10 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 168 218 (accept_3_2 19 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 168 218 2 9 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 168 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 168 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 168 218 2 8 84 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 168 218
  (Polychromatic418967fa.accept_13_2_12_10_1_2649 15 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 168 218 2 7 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 168 218 (accept_3_2 13 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 168 218 2 6 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 168 218 (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 168 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 218 2 5 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 218
  (Polychromatic418967fa.accept_13_9_12_10_1_242 9 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 218 2 4 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 218 (accept_3_2 7 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168
  218 2 3 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 218 2 2 84 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 168 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 218 2 1 84 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 218 (accept_3_2 1 168 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 168 218)))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 52 167 218 (Eq.refl Bool.true) (allA_succ_of_accept 51 167 218 (Polychromatic418967fa.accept_6_3_5_2_1_12
  51 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 167 218
  (Polychromatic418967fa.accept_20_10_7_18_1_11564 50 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 167 218 (accept_3_2 49 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 167 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 167 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 167 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 167 218 (accept_3_2 46 167 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 167 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 45
  167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 167 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 167 218 (accept_3_2 43 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 167 218 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 167 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 167 218 (accept_3_2 40 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 167 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 218
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 38 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 167 218 (accept_3_2 37 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 167 218 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 167 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 167 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 167 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 218 (accept_3_2 34 167 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 33
  167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 32 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 167 218 (accept_3_2 31 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 167 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 167 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 218 (accept_3_2 28 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 167 218
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 167 218 (accept_3_2 25 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 167 218 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 167 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 167 218 (accept_3_2 22 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 167 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 167 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 167 218 (accept_3_2 19 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 167 218 (Polychromatic418967fa.accept_11_7_2_9_1_480 18 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 218 (accept_3_2 16 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 218
  (Polychromatic418967fa.accept_13_1_11_10_1_1258 14 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 167 218 (accept_3_2 13 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 167 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 167 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 167 218 (Polychromatic418967fa.accept_19_11_15_9_1_6002 11 167
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 218 (accept_3_2 10 167
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 218 (Polychromatic418967fa.accept_4_1_3_2_1_3
  9 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 218
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 218 (accept_3_2 7 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 218 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 218 (accept_3_2 4 167 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 218 (accept_3_2 1 167 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  218)))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 53 166 218 (Eq.refl Bool.true) (allA_of_3_0 53 166
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 54 165 218 (Eq.refl Bool.true) (allA_succ_of_accept 53 165
  218 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 218 (accept_3_2 52 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 165 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 165 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 218 (accept_3_2 49 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 218 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 165 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 47 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 218 (accept_3_2 46 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 165 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 165 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 218 (accept_3_2 43 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 165 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 218 (accept_3_2 40 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 165 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 165 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 218 (accept_3_2 37 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 218 (Polychromatic418967fa.accept_19_17_13_9_1_5970 36 165 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 35 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 218 (accept_3_2 34 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 165 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 165 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 218 (accept_3_2 31 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 30 165 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 218 (accept_3_2 28 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 218 (accept_3_2 25 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 165 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 23 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 218 (accept_3_2 22 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 218 (Polychromatic418967fa.accept_25_21_15_18_1_12964 21 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 20 165 218 (Polychromatic418967fa.accept_23_20_4_11_1_2963 20 165 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 218 (accept_3_2 19 165 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 218 (Polychromatic418967fa.accept_12_6_9_2_1_311
  18 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 218 (accept_3_2 16 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 218 (accept_3_2 13 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 165 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 218
  (Polychromatic418967fa.accept_4_3_1_2_1_62 11 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 218 (accept_3_2 10 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 218 (Polychromatic418967fa.accept_17_9_12_14_1_5423 9 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 218 (accept_3_2 7 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 165 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 218 (accept_3_2 4 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 165 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 218 (accept_3_2 1 165 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165 218)))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 55 164 218
  (Eq.refl Bool.true) (allA_succ_of_gcd 54 164 218 2 27 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 164 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 164 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 218 2 26 82 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 218 2 25 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 218 (accept_3_2 49 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 218 2 24 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 164 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 218 2 23 82 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 218
  (Polychromatic418967fa.accept_11_1_10_9_1_871 45 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 218 2 22 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 218 (accept_3_2 43 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 218 2 21 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 218 (Polychromatic418967fa.accept_11_8_10_9_1_1401 41 164 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 218 2 20 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 218
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 218 2 19 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 218 (accept_3_2 37 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 218 2 18 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 164 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 35 164 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 218 2 17 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 218
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 164 218 2 16 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 164 218 (accept_3_2 31 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 164 218 2 15 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 164 218 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 164 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 164 218 2 14 82 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 164 218
  (Polychromatic418967fa.accept_31_27_9_1_1_3899 27 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 164 218 2 13 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 164 218 (accept_3_2 25 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 164 218 2 12 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 164 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 164 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 164 218 2 11 82 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 164 218
  (Polychromatic418967fa.accept_15_6_14_8_1_245 21 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 164 218 2 10 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 164 218 (accept_3_2 19 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 164 218 2 9 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 164 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 17 164 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 164 218 2 8 82 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 164 218
  (Polychromatic418967fa.accept_13_2_8_10_1_1902 15 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 164 218 2 7 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 164 218 (accept_3_2 13 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 164 218 2 6 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 164 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 164 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 218 2 5 82 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 218 2 4 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 218 (accept_3_2 7 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  218 2 3 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 164 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 218 2 2 82 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 164 218 (Polychromatic418967fa.accept_17_3_11_14_1_2071 3 164 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 218 2 1 82 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 218 (accept_3_2 1 164 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 164 218)))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 56 163 218 (Eq.refl Bool.true) (allA_of_3_0 56 163 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 57 162 218 (Eq.refl Bool.true) (allA_succ_of_gcd 56 162 218 2 28 81 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 162 218 (accept_3_2 55 162 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 162 218 2 27 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 162 218
  (Polychromatic418967fa.accept_19_15_10_9_1_5956 53 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 52 162 218 2 26 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 51 162 218 (Polychromatic418967fa.accept_12_3_6_2_1_747 51 162 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 162 218 2 25 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 162 218 (accept_3_2 49 162 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 162 218 2 24 81 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 162 218
  (Polychromatic418967fa.accept_20_7_2_18_1_5618 47 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 162 218 2 23 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 162 218 (Polychromatic418967fa.accept_10_5_2_8_1_135 45 162 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 162 218 2 22 81 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 162 218 (accept_3_2 43 162 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 162 218 2 21 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 162 218 (Polychromatic418967fa.accept_13_2_6_10_1_2703
  41 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 218 2 20 81 109
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 218 2 19 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 218 (accept_3_2 37 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 218 2 18 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 218 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 162 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 218 2 17 81 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 33 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 218 2 16 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 218 (accept_3_2 31 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 218 2 15 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 218 (Polychromatic418967fa.accept_13_3_6_10_1_2658 29 162 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 218 2 14 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 218 2 13 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 218 (accept_3_2 25 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 218 2 12 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 218 (Polychromatic418967fa.accept_19_4_10_9_1_4569 23 162 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 218 2 11 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 218
  (Polychromatic418967fa.accept_11_10_8_9_1_492 21 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 218 2 10 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 218 (accept_3_2 19 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 218 2 9 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 218 (Polychromatic418967fa.accept_13_4_6_10_1_1199 17 162 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 218 2 8 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 218
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 218 2 7 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 218 (accept_3_2 13 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 218 2 6 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 218 (Polychromatic418967fa.accept_15_11_12_8_1_739 11 162 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 218 2 5 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 218 2 4 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 218 (accept_3_2 7 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  218 2 3 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 218 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 162 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 218 2 2 81 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 218 (Polychromatic418967fa.accept_12_3_6_2_1_747 3 162 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 218 2 1 81 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 218 (accept_3_2 1 162 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162 218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 58 161 218 (Eq.refl Bool.true) (allA_succ_of_accept 57 161 218 (Polychromatic418967fa.accept_6_3_5_2_1_12
  57 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 218 (accept_3_2 55 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 218 (Polychromatic418967fa.accept_13_2_5_10_1_250 54 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 218 (Polychromatic418967fa.accept_10_3_1_8_1_132 53 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 218 (accept_3_2 52 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 161 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 218
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 218 (accept_3_2 49 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 218 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 218 (accept_3_2 46 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 218 (accept_3_2 43 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 218 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 218 (accept_3_2 40 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 218
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 38 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 218 (accept_3_2 37 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 218 (Polychromatic418967fa.accept_20_16_1_18_1_5617 36 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 218 (accept_3_2 34 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 218
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 218 (accept_3_2 31 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 218 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 218 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 218 (accept_3_2 28 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 161 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 218
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 26 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 218 (accept_3_2 25 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 218 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 218 (accept_3_2 22 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 218 (accept_3_2 19 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 218 (Polychromatic418967fa.accept_15_3_11_8_1_4186 18 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 218 (Polychromatic418967fa.accept_13_4_5_10_1_1247 17 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 218 (accept_3_2 16 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 161 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 218
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 218 (accept_3_2 13 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 218 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 218 (accept_3_2 10 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 218 (accept_3_2 7 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 218 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 218 (accept_3_2 4 161 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 161 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 218
  (Polychromatic418967fa.accept_11_2_7_9_1_890 2 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 218 (accept_3_2 1 161 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 59 160 218 (Eq.refl Bool.true) (allA_of_3_0
  59 160 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 60 159 218 (Eq.refl Bool.true) (allA_succ_of_accept 59
  159 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 58 159 218 (accept_3_2 58 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 57 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 159 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 159 218 (Polychromatic418967fa.accept_21_14_12_8_1_6833 56 159
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 218 (accept_3_2 55 159
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 218
  (Polychromatic418967fa.accept_10_4_9_8_1_125 54 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 159 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 159 218 (accept_3_2 52 159 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 159 218 (Polychromatic418967fa.accept_10_1_9_8_1_123 51 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 159 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 159 218 (accept_3_2 49 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 159 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 159 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 159 218 (accept_3_2 46 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 159 218
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 159 218 (accept_3_2 43 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 159 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 42 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 159 218 (accept_3_2 40 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 159 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 39 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 159 218
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 159 218 (accept_3_2 37 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 159 218 (Polychromatic418967fa.accept_19_17_7_9_1_3324 36 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 159 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 159 218 (accept_3_2 34 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 159 218
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 159 218 (accept_3_2 31 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 159 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 159 218 (accept_3_2 28 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 159 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 159 218
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 159 218 (accept_3_2 25 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 159 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 159 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 159 218 (accept_3_2 22 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 159 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 159 218 (accept_3_2 19 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 159 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 159 218 (accept_3_2 16 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 159 218 (Polychromatic418967fa.accept_13_2_3_10_1_658 15 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 159 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 159 218 (accept_3_2 13 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 159 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 159 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 159 218 (accept_3_2 10 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 159 218
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 159 218 (accept_3_2 7 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  159 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 159 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 159 218 (accept_3_2 4 159 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 159 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 159 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 159 218
  (Polychromatic418967fa.accept_13_2_3_10_1_658 2 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 159 218 (accept_3_2 1 159 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 159
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 61 158 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 60 158 218 2 30 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 158 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 218 2 29 79 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 218 2 28 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 218 (accept_3_2 55 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 218 2 27 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 158 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 218 2 26 79 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 218 2 25 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 218 (accept_3_2 49 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 218 2 24 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 158 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 218 2 23 79 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 218
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 218 2 22 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 218 (accept_3_2 43 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 218 2 21 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 218 (Polychromatic418967fa.accept_19_3_6_9_1_7334 41 158 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 218 2 20 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 218 2 19 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 218 (accept_3_2 37 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 218 2 18 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 158 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 218 2 17 79 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 218
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 218 2 16 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 218 (accept_3_2 31 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 218 2 15 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 218 (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 158 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 218 2 14 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 218
  (Polychromatic418967fa.accept_17_10_5_14_1_4203 27 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 158 218 2 13 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 158 218 (accept_3_2 25 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 218 2 12 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 218 (Polychromatic418967fa.accept_16_7_14_10_1_3544 23 158 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 218 2 11 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 218 2 10 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 218 (accept_3_2 19 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 218 2 9 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 158 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 218 2 8 79 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 218 2 7 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 218 (accept_3_2 13 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 218 2 6 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 218 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 158 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 218 2 5 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 218
  (Polychromatic418967fa.accept_17_9_5_14_1_4277 9 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 218 2 4 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 218 (accept_3_2 7 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  218 2 3 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 158 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 218 2 2 79 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 158 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 218 2 1 79 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 218 (accept_3_2 1 158 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 62 157 218 (Eq.refl Bool.true)
  (allA_of_3_0 62 157 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 63 156 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 62 156 218 2 31 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 156 218 (accept_3_2 61 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 218 2 30 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 156 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 218 2 29 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 218
  (Polychromatic418967fa.accept_14_1_2_8_1_655 57 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 218 2 28 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 218 (accept_3_2 55 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 218 2 27 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 156 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 218 2 26 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 218
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 218 2 25 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 218 (accept_3_2 49 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 218 2 24 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 218 (Polychromatic418967fa.accept_15_2_6_8_1_754 47 156 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 218 2 23 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 218
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 218 2 22 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 218 (accept_3_2 43 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 218 2 21 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 156 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 218 2 20 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 218
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 39 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 218 2 19 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 218 (accept_3_2 37 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 218 2 18 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 156 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 156 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 218 2 17 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 218
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 156 218 2 16 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 156 218 (accept_3_2 31 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 156 218 2 15 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 156 218 (Polychromatic418967fa.accept_11_7_2_9_1_480 29 156 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 156 218 2 14 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 156 218
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 156 218 2 13 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 156 218 (accept_3_2 25 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 156 218 2 12 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 156 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 156 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 218 2 11 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 218
  (Polychromatic418967fa.accept_16_5_12_10_1_3508 21 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 156 218 2 10 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 156 218 (accept_3_2 19 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 156 218 2 9 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 156 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 156 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 218 2 8 78 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 218
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 156 218 2 7 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 156 218 (accept_3_2 13 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 156 218 2 6 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 156 218 (Polychromatic418967fa.accept_16_11_12_10_1_3641 11 156 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 156 218 2 5 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 156 218
  (Polychromatic418967fa.accept_25_9_6_18_1_9390 9 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 156 218 2 4 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 156 218 (accept_3_2 7 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156
  218 2 3 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  156 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 156 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 156 218 2 2 78 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 156 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 156 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 156 218 2 1 78 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 156 218 (accept_3_2 1 156 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 64 155 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 63 155 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 62 155
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 155 218 (accept_3_2 61 155
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 155 218
  (Polychromatic418967fa.accept_13_8_12_10_1_4414 60 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 155 218 (Polychromatic418967fa.accept_13_7_12_10_1_640 59 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 218 (accept_3_2 58 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 155 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 56 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 218 (accept_3_2 55 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 218 (Polychromatic418967fa.accept_11_10_1_9_1_2060 54 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 155 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 218 (accept_3_2 52 155 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 218
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 50 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 155 218 (accept_3_2 49 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 155 218 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 155 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 155 218 (Polychromatic418967fa.accept_10_7_5_8_1_1167 47 155
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 218 (accept_3_2 46 155
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 218 (Polychromatic418967fa.accept_4_1_3_2_1_3
  45 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 44 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 218 (accept_3_2 43 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 155 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 218 (accept_3_2 40 155 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 218
  (Polychromatic418967fa.accept_23_15_17_11_1_7990 38 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 155 218 (accept_3_2 37 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 155 218 (Polychromatic418967fa.accept_20_16_15_18_1_5605 36 155 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 155 218
  (Polychromatic418967fa.accept_13_9_12_10_1_242 35 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 155 218 (accept_3_2 34 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 155 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 155 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 32 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 155 218 (accept_3_2 31 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 155 218 (Polychromatic418967fa.accept_14_2_1_8_1_650 30 155
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 155 218 (accept_3_2 28 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 155 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 155 218 (Polychromatic418967fa.accept_15_11_5_8_1_3157 26 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 218 (accept_3_2 25 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 155 218 (Polychromatic418967fa.accept_13_11_12_10_1_2652 24
  155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 218
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 218 (accept_3_2 22 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 218 (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 218 (accept_3_2 19 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 218 (Polychromatic418967fa.accept_15_3_5_8_1_1387 18 155
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 218 (accept_3_2 16 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 218 (Polychromatic418967fa.accept_15_14_5_8_1_3175 14 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 218 (accept_3_2 13 155 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 155
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 218
  (Polychromatic418967fa.accept_13_11_12_10_1_2652 11 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 155 218 (accept_3_2 10 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 155 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 155 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 155 218 (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 155
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 218 (accept_3_2 7 155 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 218 (Polychromatic418967fa.accept_13_6_12_10_1_690
  6 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 218 (accept_3_2 4 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 155 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 218 (accept_3_2 1 155 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155 218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 65
  154 218 (Eq.refl Bool.true) (allA_of_3_0 65 154 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 66 153 218
  (Eq.refl Bool.true) (allA_succ_of_accept 65 153 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 218 (accept_3_2 64 153 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 153 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 153 218
  (Polychromatic418967fa.accept_19_5_1_9_1_8895 62 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 153 218 (accept_3_2 61 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 153 218 (Polychromatic418967fa.accept_18_6_9_2_1_1575 60 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 153 218 (accept_3_2 58 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 153 218 (Polychromatic418967fa.accept_15_12_3_8_1_5245 57 153 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 153 218
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 153 218 (accept_3_2 55 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 153 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 54 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 153 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 153 218 (accept_3_2 52 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 153 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 153 218
  (Polychromatic418967fa.accept_15_5_3_8_1_748 50 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 153 218 (accept_3_2 49 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 153 218 (Polychromatic418967fa.accept_19_10_1_9_1_10161 48 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 218 (accept_3_2 46 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 218 (Polychromatic418967fa.accept_10_5_3_8_1_1165 45 153 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 153 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 44 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 153 218 (accept_3_2 43 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 153 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 153 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 153 218 (accept_3_2 40 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 153 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 153 218
  (Polychromatic418967fa.accept_22_16_21_20_1_11359 38 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 153 218 (accept_3_2 37 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 153 218 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 153 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 153 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 153 218 (accept_3_2 34 153 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 153 218 (Polychromatic418967fa.accept_7_5_6_1_1_407
  33 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 218
  (Polychromatic418967fa.accept_22_10_21_20_1_6534 32 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 153 218 (accept_3_2 31 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 153 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 30 153 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 218 (accept_3_2 28 153 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27
  153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 153 218
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 153 218 (accept_3_2 25 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 153 218 (Polychromatic418967fa.accept_15_9_3_8_1_3155 24 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 153 218 (accept_3_2 22 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 153 218 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 153 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 153 218
  (Polychromatic418967fa.accept_15_5_3_8_1_748 20 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 153 218 (accept_3_2 19 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 153 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 153 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 153 218 (accept_3_2 16 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 153 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 153 218
  (Polychromatic418967fa.accept_19_14_1_9_1_10328 14 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 153 218 (accept_3_2 13 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 153 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 153 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 153 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 153 218 (accept_3_2 10 153 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 153 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 153 218
  (Polychromatic418967fa.accept_11_8_10_9_1_1401 8 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 153 218 (accept_3_2 7 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  153 218 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 153 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 153 218 (accept_3_2 4 153 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 153 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 153 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 153 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 153 218 (accept_3_2 1 153 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 153
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 67 152 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 66 152 218 2 33 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 152 218 (Polychromatic418967fa.accept_10_5_2_8_1_135 65 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 152 218 2 32 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 152 218
  (Polychromatic418967fa.accept_24_15_8_2_1_9557 63 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 152 218 2 31 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 152 218 (accept_3_2 61 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 152 218 2 30 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 152 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 218 2 29 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 218 2 28 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 152 218 (accept_3_2 55 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 152 218 2 27 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 152 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 218 2 26 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 152 218 2 25 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 152 218 (accept_3_2 49 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 152 218 2 24 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 152 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 152 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 152 218 2 23 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 152 218
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 152 218 2 22 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 152 218 (accept_3_2 43 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 152 218 2 21 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 152 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 152 218 2 20 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 152 218
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 152 218 2 19 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 152 218 (accept_3_2 37 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 152 218 2 18 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 152 218 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 218 2 17 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 218 2 16 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 152 218 (accept_3_2 31 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 152 218 2 15 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 152 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 218 2 14 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 152 218 2 13 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 152 218 (accept_3_2 25 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 218 2 12 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 152 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 218 2 11 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 152 218 2 10 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 152 218 (accept_3_2 19 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 152 218 2 9 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 152 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 152 218 2 8 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 152 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 152 218 2 7 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 152 218 (accept_3_2 13 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 152 218 2 6 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 152 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 152 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 218 2 5 76 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 218
  (Polychromatic418967fa.accept_15_9_2_8_1_1379 9 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 218 2 4 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 218 (accept_3_2 7 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  218 2 3 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 218 2 2 76 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 152 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 152 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 218 2 1 76 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 218 (accept_3_2 1 152 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 152
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 68 151 218 (Eq.refl Bool.true)
  (allA_of_3_0 68 151 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 69 150 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 68 150 218 2 34 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 150 218 (accept_3_2 67 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 218 2 33 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 65 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 218 2 32 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 218 2 31 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 218 (accept_3_2 61 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 218 2 30 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 218 2 29 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 218
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 218 2 28 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 150 218 (accept_3_2 55 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 218 2 27 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 53 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 218 2 26 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 51 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 218 2 25 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 218 (accept_3_2 49 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 218 2 24 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 218 2 23 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 218 2 22 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 218 (accept_3_2 43 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 218 2 21 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 218 2 20 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 218
  (Polychromatic418967fa.accept_7_4_3_1_1_87 39 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 218 2 19 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 218 (accept_3_2 37 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 218 2 18 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 218 2 17 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 218
  (Polychromatic418967fa.accept_7_5_3_1_1_424 33 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 218 2 16 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 218 (accept_3_2 31 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 218 2 15 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 218 (Polychromatic418967fa.accept_13_3_7_10_1_668 29 150 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 218 2 14 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 218
  (Polychromatic418967fa.accept_11_5_7_9_1_2696 27 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 218 2 13 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 218 (accept_3_2 25 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 218 2 12 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 218 2 11 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 218
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 218 2 10 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 218 (accept_3_2 19 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 218 2 9 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 218 2 8 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 218 2 7 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 218 (accept_3_2 13 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 218 2 6 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 150 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 218 2 5 75 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 218 2 4 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 218 (accept_3_2 7 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  218 2 3 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 150 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 218 2 2 75 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 150 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 218 2 1 75 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 218 (accept_3_2 1 150 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 70 149 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 69 149 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 149 218 (Polychromatic418967fa.accept_12_8_5_2_1_746 68 149
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 218 (accept_3_2 67 149
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 218
  (Polychromatic418967fa.accept_7_3_2_1_1_225 66 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 149 218 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 149 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 149 218 (accept_3_2 64 149 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 149 218 (Polychromatic418967fa.accept_7_6_2_1_1_214
  62 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 218 (accept_3_2 61
  149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 60 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 149 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 149 218 (accept_3_2 58 149 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 149 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 149 218 (Polychromatic418967fa.accept_12_8_5_2_1_746
  56 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 218 (accept_3_2 55
  149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 218
  (Polychromatic418967fa.accept_10_4_9_8_1_125 54 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 53 149 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 149 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 149 218 (accept_3_2 52 149 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 51 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 149 218
  (Polychromatic418967fa.accept_15_5_14_8_1_1376 50 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 149 218 (accept_3_2 49 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 149 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 149 218 (accept_3_2 46 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 149 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 149 218
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 149 218 (accept_3_2 43 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 149 218 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 149 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 149 218 (accept_3_2 40 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 149 218
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 149 218 (accept_3_2 37 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 149 218 (Polychromatic418967fa.accept_11_3_6_9_1_1378 36 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 149 218 (accept_3_2 34 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 149 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 149 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 149 218 (accept_3_2 31 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 149 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 149 218 (Polychromatic418967fa.accept_13_3_6_10_1_2658 29 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 149 218 (accept_3_2 28 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 149 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 149 218
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 149 218 (accept_3_2 25 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 149 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 149 218 (accept_3_2 22 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 149 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 218
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 149 218 (accept_3_2 19 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 149 218 (Polychromatic418967fa.accept_13_5_6_10_1_2659 18 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 149 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 218 (accept_3_2 16 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 218
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 149 218 (accept_3_2 13 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 149 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 218 (accept_3_2 10 149 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 149 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 218
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 149 218 (accept_3_2 7 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  149 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 149 218 (Polychromatic418967fa.accept_13_5_6_10_1_2659 5 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 218 (accept_3_2 4 149 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 149 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 149 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 218
  (Polychromatic418967fa.accept_13_2_6_10_1_2703 2 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 149 218 (accept_3_2 1 149 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 71 148 218 (Eq.refl Bool.true)
  (allA_of_3_0 71 148 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 72 147 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 71 147 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 147 218 (accept_3_2 70 147 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 147 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 147 218 (Polychromatic418967fa.accept_9_5_3_2_1_171
  68 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 218 (accept_3_2 67
  147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 218
  (Polychromatic418967fa.accept_12_6_3_2_1_743 66 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 147 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 147 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 147 218 (accept_3_2 64 147 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 147 218 (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 147 218
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 147 218 (accept_3_2 61 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 147 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 147 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 147 218 (accept_3_2 58 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 147 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 147 218
  (Polychromatic418967fa.accept_15_11_12_8_1_739 56 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 147 218 (accept_3_2 55 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 147 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 147 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 147 218 (accept_3_2 52 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 147 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 147 218
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 147 218 (accept_3_2 49 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 147 218 (Polychromatic418967fa.accept_14_6_7_8_1_624 48 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 147 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 147 218 (accept_3_2 46 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 147 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 147 218
  (Polychromatic418967fa.accept_9_8_3_2_1_417 44 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 147 218 (accept_3_2 43 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 147 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 147 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 147 218 (accept_3_2 40 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 147 218 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 147 218
  (Polychromatic418967fa.accept_25_13_22_18_1_12963 38 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 147 218 (accept_3_2 37 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 147 218 (Polychromatic418967fa.accept_19_17_14_9_1_8833 36 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 35
  147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 147 218 (accept_3_2 34
  147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 147 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 33 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 147 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 147 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 218 (accept_3_2 31 147 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 147 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 29 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 218 (accept_3_2 28 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 218 (Polychromatic418967fa.accept_13_1_4_10_1_622 27 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 218 (accept_3_2 25 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 218 (accept_3_2 22 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 218 (Polychromatic418967fa.accept_13_7_4_10_1_2675 20 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 218 (accept_3_2 19 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 147
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 17 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 218 (accept_3_2 16 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 218 (accept_3_2 13 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 218 (Polychromatic418967fa.accept_16_12_3_10_1_3524 12 147 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 218
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 218 (accept_3_2 10 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 218 (accept_3_2 7 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 218
  (Polychromatic418967fa.accept_4_1_3_2_1_3 5 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 218 (accept_3_2 4 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 218 (Polychromatic418967fa.accept_15_3_12_8_1_738 3 147 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 218 (Polychromatic418967fa.accept_11_2_4_9_1_484 2 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 218 (accept_3_2 1 147 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147 218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 73 146 218 (Eq.refl Bool.true) (allA_succ_of_gcd 72 146 218 2 36 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 146 218
  (Polychromatic418967fa.accept_13_6_3_10_1_698 71 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 146 218 2 35 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 146 218 (Polychromatic418967fa.accept_17_1_10_14_1_1173 69 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 146 218 2 34 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 146 218 (accept_3_2 67 146 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 146 218 2 33 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 146 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 65 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 146 218 2 32 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 146 218 (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 146 218 2 31 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 146 218 (accept_3_2 61 146 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 146 218 2 30 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 146 218
  (Polychromatic418967fa.accept_13_7_3_10_1_656 59 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 146 218 2 29 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 146 218 (Polychromatic418967fa.accept_15_12_11_8_1_1392 57 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 146 218 2 28 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 146 218 (accept_3_2 55 146 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 146 218 2 27 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 146 218
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 146 218 2 26 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 146 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 51 146 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 146 218 2 25 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 146 218 (accept_3_2 49 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 146 218 2 24 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 146 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 47
  146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 218 2 23 73 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 218
  (Polychromatic418967fa.accept_13_6_3_10_1_698 45 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 218 2 22 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 218 (accept_3_2 43 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 218 2 21 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 218 (Polychromatic418967fa.accept_13_2_3_10_1_658 41 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 218 2 20 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 218
  (Polychromatic418967fa.accept_11_6_3_9_1_906 39 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 218 2 19 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 218 (accept_3_2 37 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 218 2 18 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 218 (Polychromatic418967fa.accept_14_7_6_8_1_2856 35 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 218 2 17 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 218
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 146 218 2 16 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 146 218 (accept_3_2 31 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 218 2 15 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 218 (Polychromatic418967fa.accept_19_10_13_9_1_4552 29 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 218 2 14 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 218
  (Polychromatic418967fa.accept_15_12_11_8_1_1392 27 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 146 218 2 13 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 146 218 (accept_3_2 25 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 218 2 12 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 146 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 218 2 11 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 218
  (Polychromatic418967fa.accept_14_7_6_8_1_2856 21 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 218 2 10 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 218 (accept_3_2 19 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 218 2 9 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 218 (Polychromatic418967fa.accept_11_6_3_9_1_906 17 146 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 218 2 8 73 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 218
  (Polychromatic418967fa.accept_13_2_3_10_1_658 15 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 218 2 7 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 218 (accept_3_2 13 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 218 2 6 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 218 (Polychromatic418967fa.accept_13_11_3_10_1_4374 11 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 218 2 5 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 218 2 4 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 218 (accept_3_2 7 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  218 2 3 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 146 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 218 2 2 73 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 218 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 146 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 218 2 1 73 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 218 (accept_3_2 1 146 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 74 145 218 (Eq.refl
  Bool.true) (allA_of_3_0 74 145 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 75 144 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 74 144 218 2 37 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 144 218 (accept_3_2 73 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 144 218 2 36 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 144 218 (Polychromatic418967fa.accept_19_14_11_9_1_3330 71 144 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 144 218 2 35 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 144 218
  (Polychromatic418967fa.accept_10_9_4_8_1_741 69 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 144 218 2 34 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 144 218 (accept_3_2 67 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 144 218 2 33 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 144 218 (Polychromatic418967fa.accept_11_10_1_9_1_2060 65 144 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 144 218 2 32 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 144 218
  (Polychromatic418967fa.accept_13_11_1_10_1_648 63 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 144 218 2 31 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 144 218 (accept_3_2 61 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 144 218 2 30 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 144 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 59 144 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 218 2 29 72 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 218
  (Polychromatic418967fa.accept_17_6_8_14_1_6706 57 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 218 2 28 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 144 218 (accept_3_2 55 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 144 218 2 27 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 144 218 (Polychromatic418967fa.accept_14_11_4_8_1_664 53 144 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 218 2 26 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 218
  (Polychromatic418967fa.accept_21_9_18_8_1_11475 51 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 144 218 2 25 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 144 218 (accept_3_2 49 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 144 218 2 24 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 144 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 47 144 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 144 218 2 23 72 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 144 218
  (Polychromatic418967fa.accept_7_3_4_1_1_71 45 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 144 218 2 22 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 144 218 (accept_3_2 43 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 144 218 2 21 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 144 218 (Polychromatic418967fa.accept_17_7_8_14_1_6720 41 144 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 218 2 20 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 218
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 218 2 19 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 218 (accept_3_2 37 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 218 2 18 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 144 218 (Polychromatic418967fa.accept_13_9_1_10_1_647 35 144 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 218 2 17 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 218
  (Polychromatic418967fa.accept_7_5_4_1_1_412 33 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 218 2 16 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 144 218 (accept_3_2 31 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 144 218 2 15 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 144 218 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 144 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 218 2 14 72 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 218
  (Polychromatic418967fa.accept_19_8_11_9_1_8827 27 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 144 218 2 13 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 144 218 (accept_3_2 25 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 144 218 2 12 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 144 218 (Polychromatic418967fa.accept_17_6_8_14_1_6706 23 144 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 144 218 2 11 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 144 218
  (Polychromatic418967fa.accept_11_10_1_9_1_2060 21 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 144 218 2 10 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 144 218 (accept_3_2 19 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 144 218 2 9 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 144 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 144 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 144 218 2 8 72 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 144 218
  (Polychromatic418967fa.accept_19_15_11_9_1_11629 15 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 144 218 2 7 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 144 218 (accept_3_2 13 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 144 218 2 6 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 144 218 (Polychromatic418967fa.accept_13_11_1_10_1_648 11 144 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 218 2 5 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 218
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 218 2 4 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 218 (accept_3_2 7 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  218 2 3 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 144 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 218 2 2 72 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 144 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 144 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 218 2 1 72 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 218 (accept_3_2 1 144 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 144
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 76 143 218 (Eq.refl
  Bool.true) (allA_succ_of_accept 75 143 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 74
  143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 218 (accept_3_2 73
  143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 72 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 143 218 (Polychromatic418967fa.accept_10_1_3_8_1_136 71 143 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 218 (accept_3_2 70 143 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 218 (Polychromatic418967fa.accept_7_5_3_1_1_424
  68 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 218 (accept_3_2 67
  143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 66 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 143 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 218 (accept_3_2 64 143 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 143 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 218
  (Polychromatic418967fa.accept_16_14_15_10_1_5910 62 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 143 218 (accept_3_2 61 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 143 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 143 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 143 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 143 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 218 (accept_3_2 58 143 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 57
  143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 218
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 56 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 143 218 (accept_3_2 55 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 143 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 218 (accept_3_2 52 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 143 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 218
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 218 (accept_3_2 49 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 218 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 47 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 218 (accept_3_2 46 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 143 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 218 (accept_3_2 43 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 218 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 218 (accept_3_2 40 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 218
  (Polychromatic418967fa.accept_17_4_7_14_1_10583 38 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 143 218 (accept_3_2 37 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 143 218 (Polychromatic418967fa.accept_10_6_3_8_1_1660 36 143 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 143 218 (Polychromatic418967fa.accept_10_5_3_8_1_1165 35 143
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 218 (accept_3_2 34 143
  218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3
  33 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 218
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 218 (accept_3_2 31 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 218 (accept_3_2 28 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 218
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 218 (accept_3_2 25 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 218 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 218 (accept_3_2 22 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 143 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 20 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 218 (accept_3_2 19 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 218 (accept_3_2 16 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 218
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 218 (accept_3_2 13 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 218 (accept_3_2 10 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 143 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 8 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 218 (accept_3_2 7 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 218 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 218 (accept_3_2 4 143 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 218 (accept_3_2 1 143 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 77 142 218 (Eq.refl
  Bool.true) (allA_of_3_0 77 142 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 78 141 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 77 141 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 141 218 (accept_3_2 76 141 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 141 218
  (Polychromatic418967fa.accept_15_14_6_8_1_1410 74 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 141 218 (accept_3_2 73 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 141 218 (Polychromatic418967fa.accept_14_2_1_8_1_650 72 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 141 218 (accept_3_2 70 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 141 218 (Polychromatic418967fa.accept_10_9_1_8_1_755 69 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 141 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 141 218 (accept_3_2 67 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 141 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 141 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 141 218 (accept_3_2 64 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 141 218
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 141 218 (accept_3_2 61 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 141 218 (Polychromatic418967fa.accept_13_8_11_10_1_636 60 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 141 218 (accept_3_2 58 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 141 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 141 218
  (Polychromatic418967fa.accept_13_4_11_10_1_1226 56 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 141 218 (accept_3_2 55 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 141 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 54 141 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 141 218 (accept_3_2 52 141 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 141 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 50 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 141 218 (accept_3_2 49 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 141 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 141 218 (accept_3_2 46 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 141 218 (Polychromatic418967fa.accept_19_7_8_9_1_7322 45 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 141 218
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 141 218 (accept_3_2 43 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 141 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 42 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 141 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 141 218 (accept_3_2 40 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 141 218
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 38 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 141 218 (accept_3_2 37 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 141 218 (Polychromatic418967fa.accept_17_2_5_14_1_2068 36 141 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 141 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 141 218 (accept_3_2 34 141 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 141 218 (Polychromatic418967fa.accept_10_3_1_8_1_132
  33 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 141 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 32 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 141 218 (accept_3_2 31 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 141 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 141 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 141 218 (accept_3_2 28 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 141 218
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 141 218 (accept_3_2 25 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 141 218 (Polychromatic418967fa.accept_21_3_15_8_1_12962 24 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 141 218 (accept_3_2 22 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 141 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 141 218
  (Polychromatic418967fa.accept_19_1_8_9_1_3304 20 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 141 218 (accept_3_2 19 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 141 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 18 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 141 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 141 218 (accept_3_2 16 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 218
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 141 218 (accept_3_2 13 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 141 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 141 218 (accept_3_2 10 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 141 218 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 141 218
  (Polychromatic418967fa.accept_9_8_6_2_1_744 8 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 141 218 (accept_3_2 7 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  141 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 6 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 141 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 141 218 (accept_3_2 4 141 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 141 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 141 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 141 218
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 2 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 141 218 (accept_3_2 1 141 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 141
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 79 140 218 (Eq.refl
  Bool.true) (allA_succ_of_gcd 78 140 218 2 39 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 77 140 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 140 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 218 2 38 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 140 218 2 37 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 140 218 (accept_3_2 73 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 140 218 2 36 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 140 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 218 2 35 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 218 2 34 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 218 (accept_3_2 67 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 218 2 33 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 218 (Polychromatic418967fa.accept_11_10_8_9_1_492 65 140 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 218 2 32 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 218
  (Polychromatic418967fa.accept_15_3_5_8_1_1387 63 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 140 218 2 31 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 140 218 (accept_3_2 61 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 218 2 30 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 59 140 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 218 2 29 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 218 2 28 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 218 (accept_3_2 55 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 218 2 27 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 140 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 218 2 26 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 218 2 25 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 218 (accept_3_2 49 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 218 2 24 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 140 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 218 2 23 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 218
  (Polychromatic418967fa.accept_16_13_12_10_1_3540 45 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 140 218 2 22 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 140 218 (accept_3_2 43 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 218 2 21 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 41 140 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 218 2 20 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 218 2 19 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 218 (accept_3_2 37 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 218 2 18 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 140 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 140 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 218 2 17 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 33 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 140 218 2 16 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 140 218 (accept_3_2 31 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 140 218 2 15 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 140 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 140 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 140 218 2 14 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 140 218
  (Polychromatic418967fa.accept_15_12_5_8_1_5247 27 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 140 218 2 13 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 140 218 (accept_3_2 25 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 140 218 2 12 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 140 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 140 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 218 2 11 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 218
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 218 2 10 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 140 218 (accept_3_2 19 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 140 218 2 9 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 140 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 218 2 8 70 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 218
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 140 218 2 7 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 140 218 (accept_3_2 13 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 140 218 2 6 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 140 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 140 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 140 218 2 5 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 140 218
  (Polychromatic418967fa.accept_17_9_4_14_1_4302 9 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 140 218 2 4 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 140 218 (accept_3_2 7 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140
  218 2 3 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  140 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 5 140 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 140 218 2 2 70 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 140 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 140 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 140 218 2 1 70 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 140 218 (accept_3_2 1 140 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 80 139 218 (Eq.refl
  Bool.true) (allA_of_3_0 80 139 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 81 138 218 (Eq.refl Bool.true)
  (allA_succ_of_gcd 80 138 218 2 40 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 218 (accept_3_2 79 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 218 2 39 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 218 2 38 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 218 2 37 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 218 (accept_3_2 73 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 218 2 36 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 218 2 35 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 69 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 218 2 34 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 218 (accept_3_2 67 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 218 2 33 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 218 (Polychromatic418967fa.accept_15_5_3_8_1_748 65 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 218 2 32 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 63 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 218 2 31 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 218 (accept_3_2 61 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 218 2 30 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 218 2 29 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 218 2 28 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 218 (accept_3_2 55 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 218 2 27 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 53 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 218 2 26 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 218
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 218 2 25 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 218 (accept_3_2 49 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 218 2 24 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 218 (Polychromatic418967fa.accept_11_3_6_9_1_1378 47 138 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 218 2 23 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 218
  (Polychromatic418967fa.accept_7_3_5_1_1_72 45 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 218 2 22 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 218 (accept_3_2 43 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 218 2 21 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 218 2 20 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 218
  (Polychromatic418967fa.accept_7_4_5_1_1_418 39 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 218 2 19 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 218 (accept_3_2 37 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 218 2 18 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 218 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 218 2 17 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 218
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 218 2 16 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 218 (accept_3_2 31 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 218 2 15 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 218 (Polychromatic418967fa.accept_37_29_27_33_1_12961 29 138 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 218 2 14 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 218 2 13 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 218 (accept_3_2 25 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 218 2 12 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 218 2 11 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 218 2 10 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 218 (accept_3_2 19 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 218 2 9 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 17 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 218 2 8 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 218
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 218 2 7 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 218 (accept_3_2 13 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 218 2 6 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 138 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 218 2 5 69 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 218 2 4 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 218 (accept_3_2 7 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  218 2 3 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 218 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 218 2 2 69 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 138 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 218 2 1 69 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 218 (accept_3_2 1 138 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 82 137 218 (Eq.refl
  Bool.true) (allA_succ_of_accept 81 137 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 137 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 80
  137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 218 (accept_3_2 79
  137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 218
  (Polychromatic418967fa.accept_17_10_1_14_1_489 78 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 137 218 (Polychromatic418967fa.accept_13_12_7_10_1_2662 77 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 137 218 (accept_3_2 76 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 218
  (Polychromatic418967fa.accept_14_4_11_8_1_2034 74 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 137 218 (accept_3_2 73 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 137 218 (Polychromatic418967fa.accept_17_4_1_14_1_4296 72 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 218 (accept_3_2 70 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 137 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 218
  (Polychromatic418967fa.accept_7_5_4_1_1_412 68 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 137 218 (accept_3_2 67 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 137 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 66 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 137 218 (Polychromatic418967fa.accept_10_5_7_8_1_1176 65 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 218 (accept_3_2 64 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 137 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 218
  (Polychromatic418967fa.accept_11_7_5_9_1_884 62 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 137 218 (accept_3_2 61 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 137 218 (Polychromatic418967fa.accept_13_8_7_10_1_4362 60 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 218 (accept_3_2 58 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 137 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 56 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 218 (accept_3_2 55 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 54 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 218 (Polychromatic418967fa.accept_18_17_11_2_1_7782 53 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 218 (accept_3_2 52 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 51 137 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 218
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 50 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 49 137 218 (accept_3_2 49 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 137 218 (Polychromatic418967fa.accept_19_10_4_9_1_7333 48 137 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 137 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 218 (accept_3_2 46 137 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 45
  137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 44 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 218 (accept_3_2 43 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 218 (Polychromatic418967fa.accept_13_3_7_10_1_668 42 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 218 (Polychromatic418967fa.accept_20_1_17_18_1_1678 41 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 218 (accept_3_2 40 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 137 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 218
  (Polychromatic418967fa.accept_7_3_4_1_1_71 38 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 218 (accept_3_2 37 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 218 (Polychromatic418967fa.accept_15_6_2_8_1_2223 36 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 218 (accept_3_2 34 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 32 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 218 (accept_3_2 31 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 218 (Polychromatic418967fa.accept_13_4_7_10_1_1200 30 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 218 (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 218 (accept_3_2 28 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 137 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 218
  (Polychromatic418967fa.accept_7_5_4_1_1_412 26 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 218 (accept_3_2 25 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 218 (accept_3_2 22 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 20 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 137 218 (accept_3_2 19 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 137 218 (Polychromatic418967fa.accept_11_7_5_9_1_884 18 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 137 218 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 218 (accept_3_2 16 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 218
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 14 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 137 218 (accept_3_2 13 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 137 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 137 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 137 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 218 (accept_3_2 10 137 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 9
  137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 218
  (Polychromatic418967fa.accept_12_8_5_2_1_746 8 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 218 (accept_3_2 7 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 218 (Polychromatic418967fa.accept_15_6_2_8_1_2223 6 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 218 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 218 (accept_3_2 4 137 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 137 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 218
  (Polychromatic418967fa.accept_19_2_4_9_1_1131 2 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 218 (accept_3_2 1 137 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 83 136 218 (Eq.refl
  Bool.true) (allA_of_3_0 83 136 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 84 135 218 (Eq.refl Bool.true)
  (allA_succ_of_accept 83 135 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 135 218 (accept_3_2 82 135 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 81 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 135 218 (Polychromatic418967fa.accept_7_3_2_1_1_225
  80 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 218 (accept_3_2 79
  135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 218
  (Polychromatic418967fa.accept_12_6_3_2_1_743 78 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 135 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 135 218 (accept_3_2 76 135 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 135 218 (Polychromatic418967fa.accept_18_3_9_2_1_5053 75 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 135 218
  (Polychromatic418967fa.accept_19_17_2_9_1_4582 74 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 135 218 (accept_3_2 73 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 135 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 72 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 135 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 135 218 (accept_3_2 70 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 135 218
  (Polychromatic418967fa.accept_19_11_2_9_1_8897 68 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 135 218 (accept_3_2 67 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 135 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 66 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 135 218 (accept_3_2 64 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 135 218 (Polychromatic418967fa.accept_10_3_5_8_1_1132 63 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 135 218
  (Polychromatic418967fa.accept_7_6_2_1_1_214 62 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 135 218 (accept_3_2 61 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 135 218 (Polychromatic418967fa.accept_13_8_5_10_1_2701 60 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 135 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 135 218 (accept_3_2 58 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 135 218
  (Polychromatic418967fa.accept_13_4_5_10_1_1247 56 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 135 218 (accept_3_2 55 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 135 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 54 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 135 218 (accept_3_2 52 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 135 218 (Polychromatic418967fa.accept_16_3_7_10_1_3503 51 135 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 135 218
  (Polychromatic418967fa.accept_11_6_3_9_1_906 50 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 135 218 (accept_3_2 49 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 135 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 48 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 135 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 135 218 (accept_3_2 46 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 135 218
  (Polychromatic418967fa.accept_26_18_5_10_1_12960 44 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 135 218 (accept_3_2 43 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 42 135 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 135 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 135 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 135 218 (accept_3_2 40 135 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 135 218 (Polychromatic418967fa.accept_11_6_3_9_1_906
  39 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 135 218
  (Polychromatic418967fa.accept_7_3_2_1_1_225 38 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 135 218 (accept_3_2 37 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 135 218 (Polychromatic418967fa.accept_17_2_16_14_1_2116 36 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 135 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 135 218 (accept_3_2 34 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 135 218
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 135 218 (accept_3_2 31 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 135 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 30 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 135 218 (accept_3_2 28 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 135 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 135 218
  (Polychromatic418967fa.accept_19_7_2_9_1_6006 26 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 135 218 (accept_3_2 25 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 135 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 135 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 135 218 (accept_3_2 22 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 135 218
  (Polychromatic418967fa.accept_7_6_2_1_1_214 20 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 135 218 (accept_3_2 19 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 135 218 (Polychromatic418967fa.accept_12_6_3_2_1_743 18 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 135 218 (accept_3_2 16 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 135 218 (Polychromatic418967fa.accept_13_2_5_10_1_250 15 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 135 218
  (Polychromatic418967fa.accept_16_14_7_10_1_898 14 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 135 218 (accept_3_2 13 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 135 218 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 135 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 135 218 (accept_3_2 10 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 135 218
  (Polychromatic418967fa.accept_13_8_5_10_1_2701 8 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 135 218 (accept_3_2 7 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  135 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 135 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 135 218 (accept_3_2 4 135 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 135 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 135 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 135 218
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 135 218 (accept_3_2 1 135 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 135
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 85 134 218
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 134 218 2 42 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 134 218 (Polychromatic418967fa.accept_13_5_4_10_1_1244 83 134
  218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 218 2 41 67 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 218
  (Polychromatic418967fa.accept_11_4_2_9_1_496 81 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 218 2 40 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 218 (accept_3_2 79 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 218 2 39 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 134 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 218 2 38 67 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 218 2 37 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 218 (accept_3_2 73 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 218 2 36 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 218 (Polychromatic418967fa.accept_13_6_4_10_1_660 71 134 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 218 2 35 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 218 2 34 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 218 (accept_3_2 67 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 218 2 33 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 218 (Polychromatic418967fa.accept_15_5_14_8_1_1376 65 134 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 218 2 32 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 218
  (Polychromatic418967fa.accept_13_11_4_10_1_3440 63 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 134 218 2 31 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 134 218 (accept_3_2 61 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 218 2 30 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 134 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 218 2 29 67 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 218 2 28 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 218 (accept_3_2 55 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 218 2 27 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 218 (Polychromatic418967fa.accept_13_1_4_10_1_622 53 134 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 218 2 26 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 51 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 218 2 25 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 218 (accept_3_2 49 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 218 2 24 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 218 (Polychromatic418967fa.accept_13_8_4_10_1_4358 47 134 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 218 2 23 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 218
  (Polychromatic418967fa.accept_13_6_4_10_1_660 45 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 218 2 22 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 218 (accept_3_2 43 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 218 2 21 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 134 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 218 2 20 67 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 218 2 19 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 218 (accept_3_2 37 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 218 2 18 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 218 (Polychromatic418967fa.accept_15_5_14_8_1_1376 35 134 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 218 2 17 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 218 2 16 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 218 (accept_3_2 31 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 218 2 15 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 218 (Polychromatic418967fa.accept_10_9_4_8_1_741 29 134 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 218 2 14 67 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 218
  (Polychromatic418967fa.accept_13_1_4_10_1_622 27 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 218 2 13 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 218 (accept_3_2 25 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 218 2 12 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 134 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 218 2 11 67 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 218
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 218 2 10 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 218 (accept_3_2 19 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 218 2 9 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 218 (Polychromatic418967fa.accept_18_17_8_2_1_2622 17 134 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 218 2 8 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 218
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 218 2 7 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 218 (accept_3_2 13 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 218 2 6 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 218 (Polychromatic418967fa.accept_13_11_4_10_1_3440 11 134 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 218 2 5 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 218
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 218 2 4 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 218 (accept_3_2 7 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  218 2 3 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 218 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 134 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 218 2 2 67 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 218 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 134 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 218 2 1 67 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 218 (accept_3_2 1 134 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 86 133 218
  (Eq.refl Bool.true) (allA_of_3_0 86 133 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 87 132 218 (Eq.refl
  Bool.true) (allA_succ_of_gcd 86 132 218 2 43 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 132 218 (accept_3_2 85 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 218 2 42 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 218 (Polychromatic418967fa.accept_13_5_2_10_1_248 83 132 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 218 2 41 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 218
  (Polychromatic418967fa.accept_13_3_2_10_1_2697 81 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 218 2 40 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 218 (accept_3_2 79 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 218 2 39 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 218 2 38 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 218
  (Polychromatic418967fa.accept_7_5_6_1_1_407 75 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 218 2 37 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 218 (accept_3_2 73 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 218 2 36 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 218 2 35 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 218
  (Polychromatic418967fa.accept_17_1_13_14_1_478 69 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 132 218 2 34 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 132 218 (accept_3_2 67 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 218 2 33 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 65 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 218 2 32 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 218
  (Polychromatic418967fa.accept_13_11_2_10_1_4399 63 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 132 218 2 31 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 132 218 (accept_3_2 61 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 218 2 30 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 218 2 29 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 218
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 218 2 28 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 218 (accept_3_2 55 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 218 2 27 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 218 2 26 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 51 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 218 2 25 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 218 (accept_3_2 49 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 218 2 24 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 47 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 218 2 23 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 218
  (Polychromatic418967fa.accept_10_5_2_8_1_135 45 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 218 2 22 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 218 (accept_3_2 43 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 218 2 21 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 218 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 218 2 20 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 218
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 218 2 19 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 218 (accept_3_2 37 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 218 2 18 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 132 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 218 2 17 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 218
  (Polychromatic418967fa.accept_7_5_6_1_1_407 33 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 132 218 2 16 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 132 218 (accept_3_2 31 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 132 218 2 15 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 132 218 (Polychromatic418967fa.accept_13_3_2_10_1_2697 29 132 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 132 218 2 14 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 132 218
  (Polychromatic418967fa.accept_17_10_13_14_1_3094 27 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 132 218 2 13 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 132 218 (accept_3_2 25 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 132 218 2 12 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 132 218 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 218 2 11 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 218
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 218 2 10 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 132 218 (accept_3_2 19 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 132 218 2 9 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 132 218 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 132 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 218 2 8 66 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 218
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 132 218 2 7 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 132 218 (accept_3_2 13 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 218 2 6 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 132 218 (Polychromatic418967fa.accept_13_11_2_10_1_4399 11 132 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 218 2 5 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 218
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 218 2 4 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 218 (accept_3_2 7 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132
  218 2 3 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 218 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 132 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 218 2 2 66 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 132 218 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 218 2 1 66 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 218 (accept_3_2 1 132 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 132
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 131 218
  (Eq.refl Bool.true) (allA_succ_of_accept 87 131 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 131 218
  (Polychromatic418967fa.accept_21_2_5_8_1_433 86 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 131 218 (accept_3_2 85 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 131 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 131 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 83 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 131 218 (accept_3_2 82 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 81 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 131 218
  (Polychromatic418967fa.accept_7_3_5_1_1_72 80 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 131 218 (accept_3_2 79 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 131 218 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 77 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 131 218 (accept_3_2 76 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 131 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 218
  (Polychromatic418967fa.accept_7_4_5_1_1_418 74 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 131 218 (accept_3_2 73 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 131 218 (Polychromatic418967fa.accept_15_12_11_8_1_1392 72 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 218 (accept_3_2 70 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 69 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 218
  (Polychromatic418967fa.accept_12_8_11_2_1_1277 68 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 131 218 (accept_3_2 67 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 131 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 66 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 65 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 218 (accept_3_2 64 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 131 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 62 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 131 218 (accept_3_2 61 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 131 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 60 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 131 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 59 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 218 (accept_3_2 58 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 57 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 131 218
  (Polychromatic418967fa.accept_11_1_10_9_1_871 56 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 131 218 (accept_3_2 55 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 131 218 (Polychromatic418967fa.accept_21_12_5_8_1_9929 54 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 53 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 131 218 (accept_3_2 52 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 131 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 131 218
  (Polychromatic418967fa.accept_13_11_1_10_1_648 50 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 131 218 (accept_3_2 49 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 131 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 48 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 131 218 (Polychromatic418967fa.accept_20_7_11_18_1_7117 47 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 131 218 (accept_3_2 46 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 45 131 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 131 218
  (Polychromatic418967fa.accept_9_8_5_2_1_422 44 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 131 218 (accept_3_2 43 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 131 218 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 41 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 131 218 (accept_3_2 40 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 131 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 131 218
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 131 218 (accept_3_2 37 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 131 218 (Polychromatic418967fa.accept_20_16_11_18_1_11530 36 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 218 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 131 218 (accept_3_2 34 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 33 131 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 131 218
  (Polychromatic418967fa.accept_7_4_5_1_1_418 32 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 131 218 (accept_3_2 31 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 131 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 29 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 131 218 (accept_3_2 28 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 131 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 131 218
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 131 218 (accept_3_2 25 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 131 218 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 131 218 (Polychromatic418967fa.accept_10_3_1_8_1_132 23 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 131 218 (accept_3_2 22 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 21 131 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 131 218
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 131 218 (accept_3_2 19 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 131 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 17 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 131 218 (accept_3_2 16 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 131 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 131 218
  (Polychromatic418967fa.accept_19_14_17_9_1_5959 14 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 131 218 (accept_3_2 13 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 131 218 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 218 (Polychromatic418967fa.accept_7_4_5_1_1_418 11 131 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 131 218 (accept_3_2 10 131 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 9
  131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 131 218
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 131 218 (accept_3_2 7 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  131 218 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 131 218 (Polychromatic418967fa.accept_4_1_3_2_1_3 5 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 131 218 (accept_3_2 4 131 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 131 218 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 131 218
  (Polychromatic418967fa.accept_19_2_17_9_1_10317 2 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 131 218 (accept_3_2 1 131 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 131
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 130 218
  (Eq.refl Bool.true) (allA_of_3_0 89 130 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 129 218 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 129 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 129 218 (accept_3_2 88 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 87 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 129 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 86 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 129 218 (accept_3_2 85 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 129 218 (Polychromatic418967fa.accept_10_4_9_8_1_125 84 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 83 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 129 218 (accept_3_2 82 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 129 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 81 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 129 218
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 129 218 (accept_3_2 79 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 129 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 129 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 129 218 (accept_3_2 76 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 75 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 129 218
  (Polychromatic418967fa.accept_7_4_3_1_1_87 74 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 129 218 (accept_3_2 73 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 129 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 72 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 71 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 129 218 (accept_3_2 70 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 129 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 129 218
  (Polychromatic418967fa.accept_7_5_3_1_1_424 68 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 129 218 (accept_3_2 67 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 129 218 (Polychromatic418967fa.accept_12_6_9_2_1_311 66 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 129 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 129 218 (accept_3_2 64 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 63 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 129 218
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 129 218 (accept_3_2 61 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 129 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 60 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 59 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 129 218 (accept_3_2 58 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 129 218 (Polychromatic418967fa.accept_10_7_9_8_1_1135 57 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 129 218
  (Polychromatic418967fa.accept_17_5_10_14_1_2083 56 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 129 218 (accept_3_2 55 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 129 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 54 129 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 129 218 (accept_3_2 52 129 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 51
  129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 129 218
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 129 218 (accept_3_2 49 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 129 218 (Polychromatic418967fa.accept_13_9_12_10_1_242 48 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 47 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 129 218 (accept_3_2 46 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 129 218 (Polychromatic418967fa.accept_13_6_12_10_1_690 45 129 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 129 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 44 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 129 218 (accept_3_2 43 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 129 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 129 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 129 218 (accept_3_2 40 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 39 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 129 218
  (Polychromatic418967fa.accept_21_17_3_8_1_6793 38 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 129 218 (accept_3_2 37 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 129 218 (Polychromatic418967fa.accept_21_15_3_8_1_6822 36 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 35 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 129 218 (accept_3_2 34 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 129 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 129 218
  (Polychromatic418967fa.accept_7_4_3_1_1_87 32 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 129 218 (accept_3_2 31 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 129 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 30 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 129 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 129 218 (accept_3_2 28 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 27 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 129 218
  (Polychromatic418967fa.accept_7_5_3_1_1_424 26 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 129 218 (accept_3_2 25 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 129 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 23 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 129 218 (accept_3_2 22 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 129 218 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 129 218
  (Polychromatic418967fa.accept_13_7_12_10_1_640 20 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 129 218 (accept_3_2 19 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 129 218 (Polychromatic418967fa.accept_7_4_3_1_1_87 18 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 129 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 129 218 (accept_3_2 16 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 15 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 129 218
  (Polychromatic418967fa.accept_9_5_3_2_1_171 14 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 129 218 (accept_3_2 13 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 129 218 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 11 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 129 218 (accept_3_2 10 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 129 218 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 129 218
  (Polychromatic418967fa.accept_9_8_3_2_1_417 8 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 129 218 (accept_3_2 7 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  129 218 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 129 218 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 129 218 (accept_3_2 4 129 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 129 218 (Polychromatic418967fa.accept_4_3_1_2_1_62 3 129 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 129 218
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 129 218 (accept_3_2 1 129 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 129
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 128 218
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 128 218 2 45 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 128 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 89 128 218
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 128 218 2 44 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 128 218
  (Polychromatic418967fa.accept_7_3_2_1_1_225 87 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 128 218 2 43 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 128 218 (accept_3_2 85 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 128 218 2 42 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 128 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 83 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 218 2 41 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 218
  (Polychromatic418967fa.accept_13_3_11_10_1_2647 81 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 80 128 218 2 40 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 79 128 218 (accept_3_2 79 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 128 218 2 39 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 128 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 77 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 218 2 38 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 218
  (Polychromatic418967fa.accept_22_9_18_20_1_12959 75 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 128 218 2 37 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 128 218 (accept_3_2 73 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 128 218 2 36 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 128 218 (Polychromatic418967fa.accept_11_5_7_9_1_2696 71 128 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 128 218 2 35 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 128 218
  (Polychromatic418967fa.accept_7_6_2_1_1_214 69 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 128 218 2 34 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 128 218 (accept_3_2 67 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 128 218 2 33 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 128 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 65 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 128 218 2 32 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 128 218
  (Polychromatic418967fa.accept_17_12_9_14_1_4283 63 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 128 218 2 31 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 128 218 (accept_3_2 61 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 128 218 2 30 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 128 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 59 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 218 2 29 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 218
  (Polychromatic418967fa.accept_11_2_7_9_1_890 57 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 218 2 28 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 128 218 (accept_3_2 55 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 128 218 2 27 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 128 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 53 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 218 2 26 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 218
  (Polychromatic418967fa.accept_13_12_11_10_1_2711 51 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 128 218 2 25 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 128 218 (accept_3_2 49 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 128 218 2 24 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 128 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 47 128 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 128 218 2 23 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 128 218
  (Polychromatic418967fa.accept_7_3_2_1_1_225 45 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 128 218 2 22 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 128 218 (accept_3_2 43 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 128 218 2 21 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 128 218 (Polychromatic418967fa.accept_7_6_2_1_1_214 41 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 128 218 2 20 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 128 218
  (Polychromatic418967fa.accept_17_5_9_14_1_4282 39 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 128 218 2 19 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 128 218 (accept_3_2 37 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 128 218 2 18 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 128 218 (Polychromatic418967fa.accept_11_2_7_9_1_890 35 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 128 218 2 17 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 128 218
  (Polychromatic418967fa.accept_20_13_8_18_1_8672 33 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 128 218 2 16 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 128 218 (accept_3_2 31 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 128 218 2 15 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 128 218 (Polychromatic418967fa.accept_12_5_8_2_1_309 29 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 128 218 2 14 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 128 218
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 128 218 2 13 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 128 218 (accept_3_2 25 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 128 218 2 12 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 128 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 23 128 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 128 218 2 11 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 128 218
  (Polychromatic418967fa.accept_13_8_11_10_1_636 21 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 128 218 2 10 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 128 218 (accept_3_2 19 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 128 218 2 9 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 128 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 128 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 128 218 2 8 64 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 128 218
  (Polychromatic418967fa.accept_13_2_11_10_1_1881 15 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 128 218 2 7 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 128 218 (accept_3_2 13 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 128 218 2 6 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 128 218 (Polychromatic418967fa.accept_12_11_8_2_1_1274 11 128 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 218 2 5 64 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 218
  (Polychromatic418967fa.accept_22_9_18_20_1_12959 9 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 128 218 2 4 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 7 128 218 (accept_3_2 7 128 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 128 218 2 3 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 128 218 (Polychromatic418967fa.accept_11_5_7_9_1_2696 5 128 218 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 128 218 2 2 64 109 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 128 218 (Polychromatic418967fa.accept_7_3_2_1_1_225 3
  128 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 218 2 1 64 109 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 218 (accept_3_2 1
  128 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 128
  218))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 127 218
  (Eq.refl Bool.true) (allA_of_3_0 92 127 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 126 218 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 126 218 2 46 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 126 218 (accept_3_2 91 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 218 2 45 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 218 (Polychromatic418967fa.accept_15_14_6_8_1_1410 89 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 218 2 44 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 87 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 218 2 43 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 218 (accept_3_2 85 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 218 2 42 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 218 (Polychromatic418967fa.accept_10_3_6_8_1_1169 83 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 218 2 41 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 81 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 218 2 40 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 218 (accept_3_2 79 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 218 2 39 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 218 (Polychromatic418967fa.accept_13_12_9_10_1_1223 77 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 218 2 38 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 75 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 218 2 37 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 218 (accept_3_2 73 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 218 2 36 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 218 (Polychromatic418967fa.accept_13_6_9_10_1_1201 71 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 218 2 35 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 69 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 218 2 34 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 218 (accept_3_2 67 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 218 2 33 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 218 (Polychromatic418967fa.accept_22_21_16_20_1_11408 65 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 218 2 32 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 218
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 63 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 218 2 31 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 218 (accept_3_2 61 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 218 2 30 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 218 (Polychromatic418967fa.accept_15_14_6_8_1_1410 59 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 218 2 29 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 57 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 218 2 28 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 218 (accept_3_2 55 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 218 2 27 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 218 (Polychromatic418967fa.accept_10_3_6_8_1_1169 53 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 218 2 26 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 218
  (Polychromatic418967fa.accept_11_7_5_9_1_884 51 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 218 2 25 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 218 (accept_3_2 49 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 218 2 24 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 218 (Polychromatic418967fa.accept_15_2_6_8_1_754 47 126 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 218 2 23 63 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 45 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 218 2 22 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 218 (accept_3_2 43 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 218 2 21 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 218 (Polychromatic418967fa.accept_19_3_12_9_1_3308 41 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 218 2 20 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 39 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 218 2 19 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 218 (accept_3_2 37 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 218 2 18 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 218 (Polychromatic418967fa.accept_19_16_12_9_1_10223 35 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 218 2 17 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 218
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 33 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 218 2 16 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 218 (accept_3_2 31 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 218 2 15 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 218 (Polychromatic418967fa.accept_11_7_5_9_1_884 29 126 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 218 2 14 63 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 27 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 218 2 13 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 218 (accept_3_2 25 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 218 2 12 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 218 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 218 2 11 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 21 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 218 2 10 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 218 (accept_3_2 19 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 218 2 9 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 218 (Polychromatic418967fa.accept_15_2_6_8_1_754 17 126 218 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 218 2 8 63 109 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 218
  (Polychromatic418967fa.accept_12_3_6_2_1_747 15 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 218 2 7 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 218 (accept_3_2 13 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 218 2 6 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 218 (Polychromatic418967fa.accept_22_11_16_20_1_12958 11 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 218 2 5 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 218
  (Polychromatic418967fa.accept_12_9_6_2_1_1273 9 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 218 2 4 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 218 (accept_3_2 7 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  218 2 3 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 218 (Polychromatic418967fa.accept_16_5_14_10_1_3644 5 126 218 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 218 2 2 63 109 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 218 (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 126 218 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 218 2 1 63 109 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 218 (accept_3_2 1 126 218
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  218)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_218_segment_000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


