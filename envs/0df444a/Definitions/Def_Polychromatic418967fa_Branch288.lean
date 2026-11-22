-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch288
-- name    : Polychromatic418967fa_Branch288
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T19:35:42.871555+00:00
-- url     : https://prove2.me/theorems/d7a2169d-74a4-4fa5-bad1-c411ec70e36d
-- title:
--   Compute
-- statement:
--   Definitions and structural lemmas for Compute, from Bhavik Mehta's pinned Polychromatic colourings of integers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch288_Segment003
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_288 : allB 288 288 :=
  allB_succ' 2 287 288 (Eq.refl Bool.true) (allA_succ_of_accept 1 287 288 (accept_3_4 1 287 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 287 288)) (allB_succ' 3 286 288 (Eq.refl Bool.true) (allA_succ_of_gcd 2 286 288 2 1 143
  144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 286 288
  (Polychromatic418967fa.accept_27_1_16_18_1_2547 1 286 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 286 288))) (allB_succ' 4 285 288 (Eq.refl Bool.true) (allA_succ_of_gcd 3 285 288 3 1 95 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 285 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 2 285 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 285 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 285 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 285 288)))) (allB_succ' 5 284 288 (Eq.refl Bool.true) (allA_succ_of_gcd 4
  284 288 4 1 71 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  3 284 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 284 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 2 284 288 2 1 142 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 284 288 (accept_3_4 1 284 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 284 288))))) (allB_succ' 6 283 288 (Eq.refl Bool.true) (allA_succ_of_accept 5 283 288 (accept_3_5 5 283 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 283 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 4
  283 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 283 288
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 283 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 283 288 (accept_3_5 2 283 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  283 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 283 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 283 288)))))) (allB_succ' 7 282 288 (Eq.refl Bool.true) (allA_succ_of_gcd 6 282 288 6 1 47 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 282 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 5 282 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 282 288 2 2 141 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 282 288 3 1 94 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 282 288 2 1 141 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 282 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448 1 282 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 282 288))))))) (allB_succ' 8 281 288 (Eq.refl Bool.true)
  (allA_succ_of_accept 7 281 288 (accept_3_4 7 281 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  281 288 (Polychromatic418967fa.accept_13_6_8_2_1_1484 6 281 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 281 288 (Polychromatic418967fa.accept_21_5_8_15_1_11890 5 281 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 281 288 (accept_3_4 4 281 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 281 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 281 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 281 288
  (Polychromatic418967fa.accept_14_2_1_8_1_650 2 281 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 281 288 (accept_3_4 1 281 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 281
  288)))))))) (allB_succ' 9 280 288 (Eq.refl Bool.true) (allA_succ_of_gcd 8 280 288 8 1 35 36 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 280 288
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 7 280 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 280 288 2 3 140 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 280 288 (accept_3_5 5 280 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 280 288 4 1 70 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 280 288 (Polychromatic418967fa.accept_21_3_7_15_1_4300 3 280 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 280 288 2 1 140 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 280 288 (Polychromatic418967fa.accept_21_1_7_15_1_4259
  1 280 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 280 288))))))))) (allB_succ' 10 279
  288 (Eq.refl Bool.true) (allA_succ_of_gcd 9 279 288 9 1 31 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 279 288 (Polychromatic418967fa.accept_13_8_6_2_1_865 8 279 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 279 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 279 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 279 288 3 2 93 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 279 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 5 279 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 279 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 279 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 279 288 3 1 93 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 279 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 2 279 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 279 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 279 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 279 288)))))))))) (allB_succ' 11 278 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 10 278 288 2 5 139 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 278 288 (Polychromatic418967fa.accept_13_9_5_2_1_2185 9 278 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 278 288 2 4 139 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 278 288 (accept_3_4 7 278 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 278 288 2 3 139 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 278 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 5
  278 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 278 288 2 2 139 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 278 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 3 278 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 278 288 2 1 139 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 278 288 (accept_3_4 1 278 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 278
  288))))))))))) (allB_succ' 12 277 288 (Eq.refl Bool.true) (allA_succ_of_accept 11 277 288 (accept_3_5 11 277 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 277 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 10
  277 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 277 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 277 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 277 288 (accept_3_5 8 277 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  277 288 (Polychromatic418967fa.accept_20_7_17_8_1_3452 7 277 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 277 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 277 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 277 288 (accept_3_5 5 277 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 277 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034 4 277 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 277 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 277 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 277 288 (accept_3_5 2 277 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  277 288 (Polychromatic418967fa.accept_17_1_5_16_1_5589 1 277 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 277 288)))))))))))) (allB_succ' 13 276 288 (Eq.refl Bool.true) (allA_succ_of_gcd 12 276 288 12 1
  23 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 276 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 276 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 276 288 2 5 138 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 276 288 3 3 92 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 276 288 4 2 69 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 276 288 (Polychromatic418967fa.accept_19_7_10_3_1_4149 7 276 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 276 288 6 1 46 48 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 276 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5
  276 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 276 288 4 1 69 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 276 288 3 1 92 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 276 288 2 1 138 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 276 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 276 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 276 288))))))))))))) (allB_succ' 14 275 288 (Eq.refl Bool.true) (allA_succ_of_accept 13 275 288 (accept_3_4
  13 275 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 275 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 12 275 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 275 288 (Polychromatic418967fa.accept_19_11_9_3_1_4167 11 275 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 275 288 (accept_3_4 10 275 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 275 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 9 275 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 275 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990
  8 275 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 275 288 (accept_3_4 7
  275 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 275 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 6 275 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 275 288 (Polychromatic418967fa.accept_20_5_15_8_1_4930 5 275 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 275 288 (accept_3_4 4 275 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 275 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 275 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 275 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 2
  275 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 275 288 (accept_3_4 1 275
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 275 288)))))))))))))) (allB_succ' 15 274 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 274 288 2 7 137 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 274 288 (Polychromatic418967fa.accept_19_13_8_3_1_2906 13 274 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 274 288 2 6 137 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 274 288 (accept_3_5 11 274 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 274 288 2 5 137 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 274 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 274 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 274 288 2 4 137 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 274 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 7 274 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 274 288 2 3 137 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 274 288 (accept_3_5 5 274 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 274 288 2 2 137 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 274 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3
  274 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 274 288 2 1 137 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 274 288
  (Polychromatic418967fa.accept_11_1_10_2_1_58 1 274 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 274 288))))))))))))))) (allB_succ' 16 273 288 (Eq.refl Bool.true) (allA_succ_of_gcd 15 273 288 3 5 91 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 273 288
  (Polychromatic418967fa.accept_19_14_7_3_1_5491 14 273 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 273 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 273 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 273 288 3 4 91 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 273 288 (Polychromatic418967fa.accept_10_1_3_8_1_136
  11 273 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 273 288
  (Polychromatic418967fa.accept_19_10_7_3_1_6977 10 273 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 9 273 288 3 3 91 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 8 273 288 (Polychromatic418967fa.accept_23_8_20_12_1_17760 8 273 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 273 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 273 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 273 288 3 2 91 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 273 288
  (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 273 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 273 288 (Polychromatic418967fa.accept_11_4_9_2_1_259 4 273 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 273 288 3 1 91 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 273 288 (Polychromatic418967fa.accept_17_2_1_16_1_6946 2 273 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 273 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 1 273 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 273 288)))))))))))))))) (allB_succ' 17 272 288 (Eq.refl Bool.true) (allA_succ_of_gcd 16 272 288 16 1 17 18
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 272 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 272 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 272 288 2 7 136 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 272 288 (accept_3_4 13 272 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 272 288 4 3 68 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 272 288 (Polychromatic418967fa.accept_22_11_8_2_1_8450 11 272 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 272 288 2 5 136 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 272 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9
  272 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 272 288 8 1 34 36 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 272 288 (accept_3_4 7
  272 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 272 288 2 3 136 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 272 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 272 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 272 288 4 1 68 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 272 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 3 272 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 272 288 2 1 136 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 272 288 (accept_3_4 1 272 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 272 288))))))))))))))))) (allB_succ' 18 271 288 (Eq.refl Bool.true)
  (allA_succ_of_accept 17 271 288 (accept_3_5 17 271 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 271 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 16 271 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 271 288 (Polychromatic418967fa.accept_22_15_7_2_1_11694 15 271 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 271 288 (accept_3_5 14 271 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 271 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 271 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 271 288
  (Polychromatic418967fa.accept_21_12_19_15_1_8942 12 271 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 271 288 (accept_3_5 11 271 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 271 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 271 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 271 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 9 271 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 271 288 (accept_3_5 8 271 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 271 288 (Polychromatic418967fa.accept_19_7_5_3_1_13861
  7 271 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 271 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 6 271 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 271 288 (accept_3_5 5 271 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  271 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 271 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 271 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 271 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 271 288 (accept_3_5 2 271 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 271 288 (Polychromatic418967fa.accept_19_1_5_3_1_6970 1 271 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 271 288)))))))))))))))))) (allB_succ' 19 270 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 18 270 288 18 1 15 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 270 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 270 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 270 288 2 8 135 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 270 288 3 5 90 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 270 288 2 7 135 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 270 288
  (Polychromatic418967fa.accept_19_13_4_3_1_2945 13 270 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 270 288 6 2 45 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 270 288 (Polychromatic418967fa.accept_13_11_10_2_1_3840 11 270 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 270 288 2 5 135 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 270 288 9 1 30 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 270 288 2 4 135 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 270 288
  (Polychromatic418967fa.accept_19_7_4_3_1_5533 7 270 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 270 288 6 1 45 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 270 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 270 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 270 288 2 2 135 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 270 288 3 1 90 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 270 288 2 1 135 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 270 288
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 1 270 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 270 288))))))))))))))))))) (allB_succ' 20 269 288 (Eq.refl Bool.true) (allA_succ_of_accept 19 269 288
  (accept_3_4 19 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 269 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 269 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 17 269 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 269 288 (accept_3_4 16 269 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 269 288 (Polychromatic418967fa.accept_17_15_14_16_1_5625 15 269 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 269 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 14 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 269 288 (accept_3_4 13 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 269 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 12 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 269 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 269 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 269 288 (accept_3_4 10 269 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 269 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 269 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 269 288
  (Polychromatic418967fa.accept_11_8_5_2_1_1629 8 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 269 288 (accept_3_4 7 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  269 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 6 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 269 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 269 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 269 288 (accept_3_4 4 269 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 269 288 (Polychromatic418967fa.accept_13_3_9_2_1_1486 3 269 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 269 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 269 288 (accept_3_4 1 269 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 269
  288)))))))))))))))))))) (allB_succ' 21 268 288 (Eq.refl Bool.true) (allA_succ_of_gcd 20 268 288 4 5 67 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 268 288
  (Polychromatic418967fa.accept_13_6_8_2_1_1484 19 268 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 268 288 2 9 134 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 268 288 (accept_3_5 17 268 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 268 288 4 4 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 268 288 (Polychromatic418967fa.accept_14_1_2_8_1_655 15 268 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 268 288 2 7 134 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 268 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13
  268 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 268 288 4 3 67 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 268 288 (accept_3_5 11
  268 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 268 288 2 5 134 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 268 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 9 268 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 268 288 4 2 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 268 288 (Polychromatic418967fa.accept_13_7_8_2_1_1483 7 268 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 268 288 2 3 134 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 268 288 (accept_3_5 5 268 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 268 288 4 1 67 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 268 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 3 268 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 268 288 2 1 134 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 268 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 1 268 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 268 288))))))))))))))))))))) (allB_succ' 22 267 288 (Eq.refl Bool.true) (allA_succ_of_gcd 21 267 288 3 7 89
  96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 267 288
  (Polychromatic418967fa.accept_22_20_3_2_1_8507 20 267 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 267 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 267 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 267 288 3 6 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 267 288 (Polychromatic418967fa.accept_15_2_12_3_1_1183
  17 267 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 267 288
  (Polychromatic418967fa.accept_14_2_1_8_1_650 16 267 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 267 288 3 5 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 267 288 (Polychromatic418967fa.accept_22_14_3_2_1_11708 14 267 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 267 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 267 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 267 288 3 4 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 267 288 (Polychromatic418967fa.accept_17_11_12_16_1_3219 11 267 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 267 288
  (Polychromatic418967fa.accept_19_10_1_3_1_12548 10 267 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 9 267 288 3 3 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 8 267 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 8 267 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 267 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873
  7 267 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 267 288 3 2 89 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 267 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 267 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 267 288 (Polychromatic418967fa.accept_19_4_1_3_1_15091 4 267 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 267 288 3 1 89 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 267 288 (Polychromatic418967fa.accept_14_2_1_8_1_650 2 267 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 267 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 267 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 267 288)))))))))))))))))))))) (allB_succ' 23 266 288 (Eq.refl Bool.true) (allA_succ_of_gcd 22 266 288 2 11
  133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 266
  288 (Polychromatic418967fa.accept_13_8_6_2_1_865 21 266 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 266 288 2 10 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 266 288 (accept_3_4 19 266 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 266 288 2 9 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 266 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 17 266 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 266 288 2 8 133 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 266 288
  (Polychromatic418967fa.accept_17_15_11_16_1_3263 15 266 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 266 288 2 7 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 266 288 (accept_3_4 13 266 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 266 288 2 6 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 266 288 (Polychromatic418967fa.accept_25_11_16_13_1_2000 11 266 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 266 288 2 5 133 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 266 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 266 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 266 288 2 4 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 266 288 (accept_3_4 7 266 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 266 288 2 3 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 266 288 (Polychromatic418967fa.accept_17_5_11_16_1_3257 5 266 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 266 288 2 2 133 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 266 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 3 266 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 266 288 2 1 133 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 266 288 (accept_3_4 1 266 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 266
  288))))))))))))))))))))))) (allB_succ' 24 265 288 (Eq.refl Bool.true) (allA_succ_of_accept 23 265 288 (accept_3_5 23
  265 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 265 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 22 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 265 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 265 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 265 288 (accept_3_5 20 265 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 265 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 265 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 265 288
  (Polychromatic418967fa.accept_21_18_13_15_1_2884 18 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 265 288 (accept_3_5 17 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 265 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 16 265 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 265 288 (Polychromatic418967fa.accept_19_15_18_3_1_1807 15 265
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 265 288 (accept_3_5 14 265
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 265 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 12 265 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 265 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 265 288 (accept_3_5 11 265 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 265 288 (Polychromatic418967fa.accept_11_10_1_2_1_1624 10 265 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 265 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 9 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 265 288 (accept_3_5 8 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  265 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 265 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844 6 265 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 265 288 (accept_3_5 5 265 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 265 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 4 265 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 265 288
  (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 265 288 (accept_3_5 2 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  265 288 (Polychromatic418967fa.accept_27_1_22_18_1_15938 1 265 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 265 288)))))))))))))))))))))))) (allB_succ' 25 264 288 (Eq.refl Bool.true) (allA_succ_of_gcd 24
  264 288 24 1 11 12 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 264 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 264 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 264 288 2 11 132 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 264 288 3 7 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 264 288 4 5 66 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 264 288 (Polychromatic418967fa.accept_10_9_4_8_1_741
  19 264 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 264 288 6 3 44 48
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 264 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 264 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 264 288 8 2 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 15 264 288 3 5 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 14 264 288 2 7 132 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 264 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 264 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 264 288 12 1 22 24 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 264 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 264 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 264 288 2 5 132 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 9 264 288 3 3 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 8 264 288 8 1 33 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 264 288 (Polychromatic418967fa.accept_21_7_12_15_1_11907 7 264 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 264 288 6 1 44 48 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 264 288
  (Polychromatic418967fa.accept_13_5_4_2_1_846 5 264 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 264 288 4 1 66 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 3 264 288 3 1 88 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_gcd 2 264 288 2 1 132 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 264 288 (Polychromatic418967fa.accept_19_1_17_3_1_1821 1 264 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 264 288))))))))))))))))))))))))) (allB_succ' 26 263 288 (Eq.refl
  Bool.true) (allA_succ_of_accept 25 263 288 (accept_3_4 25 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 263 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 24 263 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 263 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 263
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 263 288 (accept_3_4 22 263
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 263 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 21 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 263 288 (Polychromatic418967fa.accept_15_5_8_3_1_556 20 263 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 263 288 (accept_3_4 19 263 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 263 288 (Polychromatic418967fa.accept_13_5_3_2_1_1499 18 263 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 263 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 17 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 263 288 (accept_3_4 16 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 263 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 263 288 (Polychromatic418967fa.accept_13_1_3_2_1_1429 14 263 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 263 288 (accept_3_4 13 263 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 263 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 12 263 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 263 288
  (Polychromatic418967fa.accept_10_1_3_8_1_136 11 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 263 288 (accept_3_4 10 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  263 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 263 288 (Polychromatic418967fa.accept_22_8_21_2_1_8460 8 263 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 263 288 (accept_3_4 7 263 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 263 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 263 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 263 288
  (Polychromatic418967fa.accept_7_5_4_1_1_412 5 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 263 288 (accept_3_4 4 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  263 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 263 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 263 288 (Polychromatic418967fa.accept_17_2_8_16_1_4403 2 263 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 263 288 (accept_3_4 1 263 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 263 288)))))))))))))))))))))))))) (allB_succ' 27 262 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 26 262 288 2 13 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 262 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 262 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 262 288 2 12 131 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 262 288 (accept_3_5 23 262 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 262 288 2 11 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 262 288
  (Polychromatic418967fa.accept_23_21_9_12_1_14589 21 262 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 262 288 2 10 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 262 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 262 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 262 288 2 9 131 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 262 288 (accept_3_5 17 262 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 262 288 2 8 131 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 262 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 262 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 262 288 2 7 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 262 288 (Polychromatic418967fa.accept_27_13_19_18_1_10368 13 262 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 262 288 2 6 131 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 262 288 (accept_3_5 11 262 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 262 288 2 5 131 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 262 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 262 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 262 288 2 4 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 262 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 7 262 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 262 288 2 3 131 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 262 288 (accept_3_5 5 262 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 262 288 2 2 131 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 262 288 (Polychromatic418967fa.accept_17_3_7_16_1_3251
  3 262 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 262 288 2 1 131 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 262 288
  (Polychromatic418967fa.accept_21_1_10_15_1_2828 1 262 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 262 288))))))))))))))))))))))))))) (allB_succ' 28 261 288 (Eq.refl Bool.true) (allA_succ_of_gcd 27 261 288 9
  3 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 261
  288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 26 261 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 261 288 (Polychromatic418967fa.accept_13_12_1_2_1_845 25 261 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 261 288 3 8 87 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 261 288
  (Polychromatic418967fa.accept_10_3_1_8_1_132 23 261 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 261 288 (Polychromatic418967fa.accept_13_9_1_2_1_2952 22 261 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 261 288 3 7 87 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 261 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 20
  261 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 261 288
  (Polychromatic418967fa.accept_10_9_1_8_1_755 19 261 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 261 288 9 2 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 261 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 261 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 261 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 16 261
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 15 261 288 3 5 87 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 14 261 288
  (Polychromatic418967fa.accept_21_14_9_15_1_13409 14 261 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 13 261 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 261 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 261 288 3 4 87 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 261 288
  (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 261 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 261 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 261 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 261 288 9 1 29 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 261 288 (Polychromatic418967fa.accept_19_8_14_3_1_4151 8 261 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 261 288
  (Polychromatic418967fa.accept_17_7_6_16_1_2195 7 261 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 261 288 3 2 87 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 261 288 (Polychromatic418967fa.accept_11_5_8_2_1_588 5 261 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 261 288 (Polychromatic418967fa.accept_21_4_9_15_1_11925 4 261
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 261 288 3 1 87 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 261 288
  (Polychromatic418967fa.accept_21_2_9_15_1_5747 2 261 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 261 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 1 261 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 261 288)))))))))))))))))))))))))))) (allB_succ' 29 260 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 28 260 288 4 7 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 260 288 (Polychromatic418967fa.accept_19_8_13_3_1_4172 27 260 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 260 288 2 13 130 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 260 288 (accept_3_4 25 260 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 260 288 4 6 65 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 260 288
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 23 260 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 260 288 2 11 130 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 260 288 (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 260 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 260 288 4 5 65 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 260 288 (accept_3_4 19 260 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 260 288 2 9 130 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 260 288
  (Polychromatic418967fa.accept_15_2_5_3_1_552 17 260 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 260 288 4 4 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 260 288 (Polychromatic418967fa.accept_27_15_17_18_1_17689 15 260 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 260 288 2 7 130 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 260 288 (accept_3_4 13 260 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 260 288 4 3 65 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 260 288
  (Polychromatic418967fa.accept_17_11_5_16_1_5600 11 260 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 260 288 2 5 130 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 260 288 (Polychromatic418967fa.accept_11_9_7_2_1_1068 9 260 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 260 288 4 2 65 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 260 288 (accept_3_4 7 260 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 260 288 2 3 130 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 260 288 (Polychromatic418967fa.accept_21_5_8_15_1_11890
  5 260 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 260 288 4 1 65 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 260 288
  (Polychromatic418967fa.accept_21_3_8_15_1_4301 3 260 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 260 288 2 1 130 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 260 288 (accept_3_4 1 260 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 260
  288))))))))))))))))))))))))))))) (allB_succ' 30 259 288 (Eq.refl Bool.true) (allA_succ_of_accept 29 259 288
  (accept_3_5 29 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 259 288
  (Polychromatic418967fa.accept_19_9_12_3_1_2950 28 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 259 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 27 259 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 259 288 (accept_3_5 26 259 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 259 288 (Polychromatic418967fa.accept_23_2_6_12_1_17749 25 259 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 259 288
  (Polychromatic418967fa.accept_10_4_9_8_1_125 24 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 259 288 (accept_3_5 23 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 259 288 (Polychromatic418967fa.accept_15_7_4_3_1_1930 22 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 259 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 21 259 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 259 288 (accept_3_5 20 259 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 259 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 259
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 259 288
  (Polychromatic418967fa.accept_13_5_12_2_1_1423 18 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 259 288 (accept_3_5 17 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 259 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 16 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 259 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 259 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 259 288 (accept_3_5 14 259 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 13 259 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 13 259 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 259 288
  (Polychromatic418967fa.accept_21_12_7_15_1_7272 12 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 259 288 (accept_3_5 11 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 259 288 (Polychromatic418967fa.accept_13_10_12_2_1_1460 10 259 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 259 288 (Polychromatic418967fa.accept_19_9_12_3_1_2950
  9 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 259 288 (accept_3_5 8
  259 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 259 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 6 259 288 (Polychromatic418967fa.accept_13_6_12_2_1_4707 6 259 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 259 288 (accept_3_5 5 259 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 4 259 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 259 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 259 288 (Polychromatic418967fa.accept_13_3_12_2_1_385
  3 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 259 288 (accept_3_5 2
  259 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 259 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 1 259 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 259 288)))))))))))))))))))))))))))))) (allB_succ' 31 258 288 (Eq.refl Bool.true) (allA_succ_of_gcd 30 258
  288 6 5 43 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29
  258 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 258 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 258 288 2 14 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 27 258 288 3 9 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 26 258 288 2 13 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 258 288 (Polychromatic418967fa.accept_21_4_6_15_1_5744 25 258
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 258 288 6 4 43 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 258 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 23 258 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 258 288 2 11 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 21 258 288 3 7 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 20 258 288 2 10 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 258 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 19 258 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 258 288 6 3 43 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 258 288
  (Polychromatic418967fa.accept_13_4_11_2_1_1458 17 258 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 258 288 2 8 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 15 258 288 3 5 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 14 258 288 2 7 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 258 288 (Polychromatic418967fa.accept_17_13_3_16_1_5599 13 258 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 258 288 6 2 43 48 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 258 288
  (Polychromatic418967fa.accept_20_11_18_8_1_4821 11 258 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 258 288 2 5 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 9 258 288 3 3 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 8 258 288 2 4 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 258 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 7 258 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 258 288 6 1 43 48 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 258 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 258 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 258 288 2 2 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 3 258 288 3 1 86 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 2 258 288 2 1 129 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 1 258 288 (Polychromatic418967fa.accept_19_1_11_3_1_5463 1 258 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 258 288))))))))))))))))))))))))))))))) (allB_succ' 32
  257 288 (Eq.refl Bool.true) (allA_succ_of_accept 31 257 288 (accept_3_4 31 257 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 257 288 (Polychromatic418967fa.accept_19_11_10_3_1_2934 30 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 257 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 29 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 257 288 (accept_3_4 28 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 257 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 27 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 257 288 (Polychromatic418967fa.accept_19_7_10_3_1_4149 26 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 257 288 (accept_3_4 25 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 257 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 24 257 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 257 288
  (Polychromatic418967fa.accept_22_1_15_2_1_3668 23 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 257 288 (accept_3_4 22 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 257 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 257 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 20 257 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 257 288 (accept_3_4 19 257 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 18 257 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 18 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 257 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 17 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 257 288 (accept_3_4 16 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 257 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 257 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980 14 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 257 288 (accept_3_4 13 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 257 288 (Polychromatic418967fa.accept_13_12_10_2_1_1451 12 257
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 257 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 257 288 (accept_3_4 10 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  257 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 257 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 8 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 257 288 (accept_3_4 7 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 257 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 6 257 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 257 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 5 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 257 288 (accept_3_4 4 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  257 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 257 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 257 288 (Polychromatic418967fa.accept_23_2_4_12_1_17854 2 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 257 288 (accept_3_4 1 257 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 257 288)))))))))))))))))))))))))))))))) (allB_succ' 33 256 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 32 256 288 32 1 8 9 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 256 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 31 256 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 256 288 2 15 128 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 256 288 (accept_3_5 29 256 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 256 288 4 7 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 256 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448
  27 256 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 256 288 2 13 128 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 256 288
  (Polychromatic418967fa.accept_14_11_4_8_1_664 25 256 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 256 288 8 3 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 256 288 (accept_3_5 23 256 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22
  256 288 2 11 128 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 21 256 288 (Polychromatic418967fa.accept_15_6_1_3_1_2852 21 256 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 256 288 4 5 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 256 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19
  256 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 256 288 2 9 128 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 256 288 (accept_3_5 17
  256 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 256 288 16 1 16 18 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 256 288
  (Polychromatic418967fa.accept_17_15_1_16_1_8166 15 256 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 256 288 2 7 128 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 256 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 256 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 256 288 4 3 64 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 256 288 (accept_3_5 11 256 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 256 288 2 5 128 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 256 288
  (Polychromatic418967fa.accept_21_9_4_15_1_5801 9 256 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 256 288 8 1 32 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 256 288 (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 256 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 256 288 2 3 128 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 256 288 (accept_3_5 5 256 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 4 256 288 4 1 64 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 256 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 3 256 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 256 288 2 1 128 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 256 288
  (Polychromatic418967fa.accept_11_1_3_2_1_1090 1 256 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 256 288))))))))))))))))))))))))))))))))) (allB_succ' 34 255 288 (Eq.refl Bool.true) (allA_succ_of_gcd 33 255
  288 3 11 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32
  255 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 32 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 255 288 (Polychromatic418967fa.accept_21_10_3_15_1_13463 31 255 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 255 288 3 10 85 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 255 288
  (Polychromatic418967fa.accept_21_8_3_15_1_2875 29 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 255 288 (Polychromatic418967fa.accept_21_7_3_15_1_5800 28 255 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 255 288 3 9 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 255 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 26
  255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 255 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 25 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 255 288 3 8 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 255 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 255 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 255 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 22 255
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 255 288 3 7 85 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 255 288
  (Polychromatic418967fa.accept_13_7_8_2_1_1483 20 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 255 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 255 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 255 288 3 6 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 255 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167
  17 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 255 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 16 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 255 288 3 5 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 255 288 (Polychromatic418967fa.accept_19_14_8_3_1_6981 14 255 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 255 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 13 255
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 255 288 3 4 85 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 255 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 11 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 255 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 10 255 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 255 288 3 3 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 255 288 (Polychromatic418967fa.accept_21_8_3_15_1_2875 8 255 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 255 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 7 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 255 288 3 2 85 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 255 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 255 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 255 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 255 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 255 288 3 1 85 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 255 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 2 255 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 255 288 (Polychromatic418967fa.accept_21_1_3_15_1_5797 1 255 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 255 288)))))))))))))))))))))))))))))))))) (allB_succ' 35 254 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 34 254 288 2 17 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 33 254 288 (Polychromatic418967fa.accept_19_14_7_3_1_5491 33 254 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 254 288 2 16 127 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 254 288 (accept_3_4 31 254 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 254 288 2 15 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 254 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 29 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 254 288 2 14 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 254 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 27 254 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 254 288 2 13 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 254 288 (accept_3_4 25 254 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 254 288 2 12 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 254 288 (Polychromatic418967fa.accept_19_4_7_3_1_2893
  23 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 254 288 2 11 127 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 254 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 21 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 254 288 2 10 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 254 288 (accept_3_4 19 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 254 288 2 9 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 254 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 17 254 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 254 288 2 8 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 254 288
  (Polychromatic418967fa.accept_14_1_2_8_1_655 15 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 254 288 2 7 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 254 288 (accept_3_4 13 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 254 288 2 6 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 254 288 (Polychromatic418967fa.accept_15_11_14_3_1_1965 11 254 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 254 288 2 5 127 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 254 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 9 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 254 288 2 4 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 254 288 (accept_3_4 7 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 254 288 2 3 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 254 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 5 254 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 254 288 2 2 127 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 254 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 254 288 2 1 127 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 254 288 (accept_3_4 1 254 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 254
  288))))))))))))))))))))))))))))))))))) (allB_succ' 36 253 288 (Eq.refl Bool.true) (allA_succ_of_accept 35 253 288
  (accept_3_5 35 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 253 288
  (Polychromatic418967fa.accept_13_8_6_2_1_865 34 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 253 288 (Polychromatic418967fa.accept_21_12_1_15_1_8924 33 253 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 253 288 (accept_3_5 32 253 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 253 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 31 253 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 253 288
  (Polychromatic418967fa.accept_13_4_6_2_1_1437 30 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 253 288 (accept_3_5 29 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 253 288 (Polychromatic418967fa.accept_17_11_15_16_1_4377 28 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 253 288 (Polychromatic418967fa.accept_13_1_6_2_1_377 27 253 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 253 288 (accept_3_5 26 253 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 253 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 25 253
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 253 288
  (Polychromatic418967fa.accept_15_9_13_3_1_535 24 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 253 288 (accept_3_5 23 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 253 288 (Polychromatic418967fa.accept_13_9_6_2_1_2200 22 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 253 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 21 253 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 253 288 (accept_3_5 20 253 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 253 288 (Polychromatic418967fa.accept_21_19_1_15_1_11887 19
  253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 253 288
  (Polychromatic418967fa.accept_17_1_15_16_1_2202 18 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 253 288 (accept_3_5 17 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 253 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 253 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 253 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 15 253
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 253 288 (accept_3_5 14 253
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 253 288
  (Polychromatic418967fa.accept_22_13_11_2_1_17853 13 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 253 288 (Polychromatic418967fa.accept_13_12_6_2_1_1441 12 253 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 253 288 (accept_3_5 11 253 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 253 288 (Polychromatic418967fa.accept_13_10_6_2_1_1440 10 253
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 253 288
  (Polychromatic418967fa.accept_13_9_6_2_1_2200 9 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 253 288 (accept_3_5 8 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  253 288 (Polychromatic418967fa.accept_14_7_1_8_1_2873 7 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 253 288 (Polychromatic418967fa.accept_10_6_3_8_1_1660 6 253 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 253 288 (accept_3_5 5 253 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 253 288 (Polychromatic418967fa.accept_13_4_6_2_1_1437 4 253 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 253 288
  (Polychromatic418967fa.accept_20_3_13_8_1_12215 3 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 253 288 (accept_3_5 2 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  253 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 253 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 253 288)))))))))))))))))))))))))))))))))))) (allB_succ' 37 252 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 36 252 288 36 1 7 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 252 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 35 252 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 252 288 2 17 126 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 252 288 3 11 84 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 252 288 4 8 63 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 252 288
  (Polychromatic418967fa.accept_25_6_2_13_1_17852 31 252 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 30 252 288 6 5 42 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 29 252 288 (Polychromatic418967fa.accept_13_3_5_2_1_1475 29 252 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 252 288 4 7 63 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 252 288 9 3 28 32 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 252 288 2 13 126 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 252 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 25 252 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 252 288 12 2 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 252 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 23 252 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 252 288 2 11 126 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 252 288 3 7 84 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 252 288 4 5 63 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 252 288
  (Polychromatic418967fa.accept_17_2_14_16_1_2187 19 252 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 252 288 18 1 14 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 252 288 (Polychromatic418967fa.accept_13_4_5_2_1_1436 17 252 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 252 288 4 4 63 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 252 288 3 5 84 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 252 288 2 7 126 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 252 288
  (Polychromatic418967fa.accept_15_13_12_3_1_1180 13 252 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 252 288 12 1 21 24 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 252 288 (Polychromatic418967fa.accept_17_11_14_16_1_1270 11 252 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 252 288 2 5 126 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 252 288 9 1 28 32 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 252 288 4 2 63 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 252 288
  (Polychromatic418967fa.accept_13_7_5_2_1_401 7 252 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 252 288 6 1 42 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 252 288 (Polychromatic418967fa.accept_10_5_2_8_1_135 5 252 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 252 288 4 1 63 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 252 288 3 1 84 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 252 288 2 1 126 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 252 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 1
  252 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 252
  288))))))))))))))))))))))))))))))))))))) (allB_succ' 38 251 288 (Eq.refl Bool.true) (allA_succ_of_accept 37 251 288
  (accept_3_4 37 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 251 288
  (Polychromatic418967fa.accept_15_6_11_3_1_1172 36 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 251 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 35 251 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 251 288 (accept_3_4 34 251 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 251 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 33 251 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 251 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433
  32 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 251 288 (accept_3_4 31
  251 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 251 288
  (Polychromatic418967fa.accept_7_2_6_1_1_73 30 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 251 288 (Polychromatic418967fa.accept_10_9_1_8_1_755 29 251 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 251 288 (accept_3_4 28 251 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 251 288 (Polychromatic418967fa.accept_19_8_4_3_1_5559 27 251 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 251 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 26 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 251 288 (accept_3_4 25 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 251 288 (Polychromatic418967fa.accept_13_11_4_2_1_2954 24 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 251 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 23 251 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 251 288 (accept_3_4 22 251 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 251 288 (Polychromatic418967fa.accept_14_7_13_8_1_2067 21 251 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 251 288
  (Polychromatic418967fa.accept_17_3_13_16_1_2183 20 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 251 288 (accept_3_4 19 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 251 288 (Polychromatic418967fa.accept_11_7_9_2_1_260 18 251 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 251 288 (Polychromatic418967fa.accept_20_17_11_8_1_4894 17 251
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 251 288 (accept_3_4 16 251
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 251 288
  (Polychromatic418967fa.accept_11_4_9_2_1_259 15 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 251 288 (Polychromatic418967fa.accept_15_14_11_3_1_1957 14 251 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 251 288 (accept_3_4 13 251 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 251 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 12 251 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 251 288
  (Polychromatic418967fa.accept_13_11_4_2_1_2954 11 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 251 288 (accept_3_4 10 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  251 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 251 288 (Polychromatic418967fa.accept_15_8_11_3_1_3847 8 251 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 251 288 (accept_3_4 7 251 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 251 288 (Polychromatic418967fa.accept_13_6_4_2_1_1433 6 251 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 251 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 5 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 251 288 (accept_3_4 4 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  251 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 251 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 251 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 2 251 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 251 288 (accept_3_4 1 251 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 251 288)))))))))))))))))))))))))))))))))))))) (allB_succ' 39 250 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 38 250 288 2 19 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 37 250 288 (Polychromatic418967fa.accept_13_11_3_2_1_863 37 250 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 250 288 2 18 125 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 250 288 (accept_3_5 35 250 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 250 288 2 17 125 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 250 288
  (Polychromatic418967fa.accept_21_12_19_15_1_8942 33 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 250 288 2 16 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 250 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31 250 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 250 288 2 15 125 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 250 288 (accept_3_5 29 250 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 250 288 2 14 125 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 250 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 27 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 250 288 2 13 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 250 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 250 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 250 288 2 12 125 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 250 288 (accept_3_5 23 250 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 250 288 2 11 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 250 288 (Polychromatic418967fa.accept_15_6_10_3_1_2844
  21 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 250 288 2 10 125 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 250 288
  (Polychromatic418967fa.accept_27_19_7_18_1_4284 19 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 18 250 288 2 9 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 17 250 288 (accept_3_5 17 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 250 288 2 8 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 15 250 288 (Polychromatic418967fa.accept_20_15_10_8_1_6398 15 250 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 250 288 2 7 125 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 250 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 13 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 250 288 2 6 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 250 288 (accept_3_5 11 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 250 288 2 5 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 250 288 (Polychromatic418967fa.accept_13_9_3_2_1_399 9 250 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 250 288 2 4 125 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 250 288
  (Polychromatic418967fa.accept_15_7_10_3_1_2891 7 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 250 288 2 3 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 250 288 (accept_3_5 5 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 250 288 2 2 125 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 250 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 3 250 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 250 288 2 1 125 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 250 288
  (Polychromatic418967fa.accept_13_1_3_2_1_1429 1 250 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 250 288))))))))))))))))))))))))))))))))))))))) (allB_succ' 40 249 288 (Eq.refl Bool.true) (allA_succ_of_gcd
  39 249 288 3 13 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 38 249 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 38 249 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 249 288 (Polychromatic418967fa.accept_10_7_9_8_1_1135 37 249
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 249 288 3 12 83 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 249 288
  (Polychromatic418967fa.accept_15_5_9_3_1_528 35 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 249 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 34 249 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 33 249 288 3 11 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 32 249 288 (Polychromatic418967fa.accept_14_4_11_8_1_2034
  32 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 249 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 31 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 249 288 3 10 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 249 288 (Polychromatic418967fa.accept_17_12_11_16_1_6903 29 249 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 249 288
  (Polychromatic418967fa.accept_15_13_9_3_1_1949 28 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 27 249 288 3 9 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 26 249 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 26 249 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 249 288 (Polychromatic418967fa.accept_15_10_9_3_1_1947 25 249
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 249 288 3 8 83 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 249 288
  (Polychromatic418967fa.accept_15_8_9_3_1_1194 23 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 249 288 (Polychromatic418967fa.accept_17_5_11_16_1_3257 22 249 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 249 288 3 7 83 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 249 288
  (Polychromatic418967fa.accept_11_9_7_2_1_1068 20 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 249 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 19 249 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 249 288 3 6 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 249 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17
  249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 249 288
  (Polychromatic418967fa.accept_19_16_2_3_1_5479 16 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 249 288 3 5 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 249 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 14 249 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 249 288 (Polychromatic418967fa.accept_15_13_9_3_1_1949 13 249
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 249 288 3 4 83 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 249 288
  (Polychromatic418967fa.accept_10_1_9_8_1_123 11 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 249 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 10 249 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 249 288 3 3 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 249 288 (Polychromatic418967fa.accept_15_8_9_3_1_1194 8 249 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 249 288
  (Polychromatic418967fa.accept_10_7_9_8_1_1135 7 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 249 288 3 2 83 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 249 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 249 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 249 288 (Polychromatic418967fa.accept_10_4_9_8_1_125 4 249 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 249 288 3 1 83 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 249 288
  (Polychromatic418967fa.accept_21_2_18_15_1_4236 2 249 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 249 288 (Polychromatic418967fa.accept_10_1_9_8_1_123 1 249 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 249 288)))))))))))))))))))))))))))))))))))))))) (allB_succ' 41 248 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 40 248 288 8 5 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 248 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 248 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 248 288 2 19 124 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 248 288 (accept_3_4 37 248 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 248 288 4 9 62 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 248 288
  (Polychromatic418967fa.accept_13_9_1_2_1_2952 35 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 248 288 2 17 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 248 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 248 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 248 288 8 4 31 36 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 248 288 (accept_3_4 31 248 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 248 288 2 15 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 248 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960
  29 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 248 288 4 7 62 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 248 288
  (Polychromatic418967fa.accept_15_12_8_3_1_1995 27 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 248 288 2 13 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 248 288 (accept_3_4 25 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 248 288 8 3 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 248 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 23 248 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 248 288 2 11 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 248 288 (Polychromatic418967fa.accept_19_2_1_3_1_11216
  21 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 248 288 4 5 62 72
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 248 288
  (accept_3_4 19 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 248 288 2 9 124 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 248 288
  (Polychromatic418967fa.accept_19_17_1_3_1_4160 17 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 248 288 8 2 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 248 288 (Polychromatic418967fa.accept_11_4_6_2_1_51 15 248 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 248 288 2 7 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 248 288 (accept_3_4 13 248 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 248 288 4 3 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 248 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 11 248 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 248 288 2 5 124 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 248 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 9 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 248 288 8 1 31 36 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 248 288 (accept_3_4 7 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 248
  288 2 3 124 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  248 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 5 248 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 248 288 4 1 62 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 248 288 (Polychromatic418967fa.accept_13_3_1_2_1_2960 3 248 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 248 288 2 1 124 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 248 288 (accept_3_4 1 248 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 248 288))))))))))))))))))))))))))))))))))))))))) (allB_succ' 42 247 288
  (Eq.refl Bool.true) (allA_succ_of_accept 41 247 288 (accept_3_5 41 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 247 288 (Polychromatic418967fa.accept_15_10_7_3_1_1939 40 247 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 247 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 39 247
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 247 288 (accept_3_5 38 247
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 247 288
  (Polychromatic418967fa.accept_20_17_7_8_1_7919 37 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 247 288 (Polychromatic418967fa.accept_27_9_4_18_1_17837 36 247 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 247 288 (accept_3_5 35 247 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 34 247 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 34 247 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 247 288
  (Polychromatic418967fa.accept_22_11_5_2_1_3658 33 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 247 288 (accept_3_5 32 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  31 247 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 31 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 247 288 (Polychromatic418967fa.accept_11_8_5_2_1_1629 30 247 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 247 288 (accept_3_5 29 247 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 247 288 (Polychromatic418967fa.accept_23_5_17_12_1_3008 28 247
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 247 288
  (Polychromatic418967fa.accept_7_6_2_1_1_214 27 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 247 288 (accept_3_5 26 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  25 247 288 (Polychromatic418967fa.accept_10_5_7_8_1_1176 25 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 247 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 24 247 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 247 288 (accept_3_5 23 247 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 22 247 288 (Polychromatic418967fa.accept_21_1_16_15_1_8913 22 247 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 247 288
  (Polychromatic418967fa.accept_20_1_7_8_1_4877 21 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 247 288 (accept_3_5 20 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  19 247 288 (Polychromatic418967fa.accept_10_9_7_8_1_1184 19 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 247 288 (Polychromatic418967fa.accept_21_18_16_15_1_2864 18 247 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 247 288 (accept_3_5 17 247 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 247 288 (Polychromatic418967fa.accept_25_16_22_13_1_17851 16
  247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 247 288
  (Polychromatic418967fa.accept_10_5_7_8_1_1176 15 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 247 288 (accept_3_5 14 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  13 247 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 13 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 247 288 (Polychromatic418967fa.accept_15_12_7_3_1_1940 12 247 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 247 288 (accept_3_5 11 247 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 247 288 (Polychromatic418967fa.accept_7_3_2_1_1_225 10 247 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 247 288
  (Polychromatic418967fa.accept_10_9_7_8_1_1184 9 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 8 247 288 (accept_3_5 8 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7
  247 288 (Polychromatic418967fa.accept_22_7_5_2_1_17844 7 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 6 247 288 (Polychromatic418967fa.accept_7_6_2_1_1_214 6 247 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 247 288 (accept_3_5 5 247 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 4 247 288 (Polychromatic418967fa.accept_15_4_7_3_1_119 4 247 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 247 288
  (Polychromatic418967fa.accept_7_3_2_1_1_225 3 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 2 247 288 (accept_3_5 2 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1
  247 288 (Polychromatic418967fa.accept_14_1_9_8_1_2863 1 247 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_one 247 288)))))))))))))))))))))))))))))))))))))))))) (allB_succ' 43 246 288 (Eq.refl Bool.true)
  (allA_succ_of_gcd 42 246 288 6 7 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 41 246 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 41 246 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 246 288 2 20 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 39 246 288 3 13 82 96 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 38 246 288 2 19 123 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 246 288
  (Polychromatic418967fa.accept_23_14_16_12_1_17850 37 246 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 36 246 288 6 6 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 35 246 288 (Polychromatic418967fa.accept_15_5_6_3_1_525 35 246 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 246 288 2 17 123 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 33 246 288 3 11 82 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 32 246 288 2 16 123 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 246 288
  (Polychromatic418967fa.accept_11_9_4_2_1_600 31 246 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 246 288 6 5 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 246 288 (Polychromatic418967fa.accept_13_3_12_2_1_385 29 246 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 246 288 2 14 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 27 246 288 3 9 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 26 246 288 2 13 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 246 288
  (Polychromatic418967fa.accept_15_10_6_3_1_1160 25 246 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 246 288 6 4 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 246 288 (Polychromatic418967fa.accept_10_3_6_8_1_1169 23 246 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 246 288 2 11 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 21 246 288 3 7 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 20 246 288 2 10 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 246 288
  (Polychromatic418967fa.accept_13_6_12_2_1_4707 19 246 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 246 288 6 3 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 246 288 (Polychromatic418967fa.accept_11_6_4_2_1_599 17 246 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 246 288 2 8 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 15 246 288 3 5 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 14 246 288 2 7 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 246 288
  (Polychromatic418967fa.accept_10_3_6_8_1_1169 13 246 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 246 288 6 2 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 246 288 (Polychromatic418967fa.accept_15_11_6_3_1_1192 11 246 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 246 288 2 5 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 9 246 288 3 3 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 8 246 288 2 4 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 246 288
  (Polychromatic418967fa.accept_17_7_8_16_1_6966 7 246 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 246 288 6 1 41 48 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 246 288 (Polychromatic418967fa.accept_13_5_12_2_1_1423 5 246 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 246 288 2 2 123 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 3 246 288 3 1 82 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 2 246 288 2 1 123 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 246 288
  (Polychromatic418967fa.accept_13_1_12_2_1_384 1 246 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_one 246 288))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 44 245 288 (Eq.refl Bool.true)
  (allA_succ_of_accept 43 245 288 (accept_3_4 43 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 245 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 42 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 245 288 (Polychromatic418967fa.accept_14_13_7_8_1_677 41 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 245 288 (accept_3_4 40 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 245 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 39 245
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 245 288
  (Polychromatic418967fa.accept_15_8_5_3_1_1990 38 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 245 288 (accept_3_4 37 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 245 288 (Polychromatic418967fa.accept_13_10_11_2_1_3862 36 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 245 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 35 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 245 288 (accept_3_4 34 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 245 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 33 245
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 245 288
  (Polychromatic418967fa.accept_10_2_5_8_1_139 32 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 245 288 (accept_3_4 31 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 245 288 (Polychromatic418967fa.accept_13_4_11_2_1_1458 30 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 245 288 (Polychromatic418967fa.accept_13_3_11_2_1_1422 29 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 245 288 (accept_3_4 28 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 245 288 (Polychromatic418967fa.accept_10_7_5_8_1_1167 27 245
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 245 288
  (Polychromatic418967fa.accept_21_5_14_15_1_7290 26 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 25 245 288 (accept_3_4 25 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 24 245 288 (Polychromatic418967fa.accept_15_9_5_3_1_554 24 245 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 245 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 23 245
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 245 288 (accept_3_4 22 245
  288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 245 288
  (Polychromatic418967fa.accept_15_6_5_3_1_1988 21 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 245 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 20 245 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 245 288 (accept_3_4 19 245 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 245 288 (Polychromatic418967fa.accept_21_18_14_15_1_5809 18 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 245 288
  (Polychromatic418967fa.accept_10_7_5_8_1_1167 17 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 245 288 (accept_3_4 16 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 245 288 (Polychromatic418967fa.accept_14_1_7_8_1_2063 15 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 245 288 (Polychromatic418967fa.accept_19_14_17_3_1_4137 14 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 245 288 (accept_3_4 13 245 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 245 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 12 245
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 245 288
  (Polychromatic418967fa.accept_22_11_3_2_1_17849 11 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 10 245 288 (accept_3_4 10 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 9 245 288 (Polychromatic418967fa.accept_13_9_11_2_1_1491 9 245 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 245 288 (Polychromatic418967fa.accept_15_8_5_3_1_1990 8 245 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 245 288 (accept_3_4 7 245 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 245 288 (Polychromatic418967fa.accept_14_6_7_8_1_624 6
  245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 245 288
  (Polychromatic418967fa.accept_19_5_17_3_1_4152 5 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 245 288 (accept_3_4 4 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  245 288 (Polychromatic418967fa.accept_10_3_5_8_1_1132 3 245 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 245 288 (Polychromatic418967fa.accept_10_2_5_8_1_139 2 245 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 245 288 (accept_3_4 1 245 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 245 288)))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 45 244 288 (Eq.refl
  Bool.true) (allA_succ_of_gcd 44 244 288 4 11 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 244 288 (Polychromatic418967fa.accept_17_9_6_16_1_3280 43 244 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 244 288 2 21 122 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 244 288 (accept_3_5 41 244 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 244 288 4 10 61 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 244 288
  (Polychromatic418967fa.accept_10_9_4_8_1_741 39 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 244 288 2 19 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 244 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 37 244 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 244 288 4 9 61 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 244 288 (accept_3_5 35 244 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 244 288 2 17 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 244 288 (Polychromatic418967fa.accept_7_5_6_1_1_407 33
  244 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 244 288 4 8 61 72 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 244 288
  (Polychromatic418967fa.accept_13_5_10_2_1_856 31 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 244 288 2 15 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 244 288 (accept_3_5 29 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 244 288 4 7 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 244 288 (Polychromatic418967fa.accept_17_10_6_16_1_6862 27 244 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 244 288 2 13 122 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 244 288
  (Polychromatic418967fa.accept_13_12_10_2_1_1451 25 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 24 244 288 4 6 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 23 244 288 (accept_3_5 23 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 244 288 2 11 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 244 288 (Polychromatic418967fa.accept_13_8_10_2_1_1450 21 244 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 244 288 4 5 61 72 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 244 288
  (Polychromatic418967fa.accept_7_5_6_1_1_407 19 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 244 288 2 9 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 244 288 (accept_3_5 17 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 244 288 4 4 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 244 288 (Polychromatic418967fa.accept_19_15_16_3_1_8409 15 244 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 244 288 2 7 122 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 244 288
  (Polychromatic418967fa.accept_19_13_16_3_1_6983 13 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 12 244 288 4 3 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 11 244 288 (accept_3_5 11 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 244 288 2 5 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 244 288 (Polychromatic418967fa.accept_7_2_6_1_1_73 9 244 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 244 288 4 2 61 72 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 244 288 (Polychromatic418967fa.accept_14_7_6_8_1_2856 7
  244 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 244 288 2 3 122 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 244 288 (accept_3_5 5
  244 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 244 288 4 1 61 72 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 244 288
  (Polychromatic418967fa.accept_13_3_10_2_1_381 3 244 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 244 288 2 1 122 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 244 288 (Polychromatic418967fa.accept_15_1_4_3_1_1928 1 244 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 244 288))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 46
  243 288 (Eq.refl Bool.true) (allA_succ_of_gcd 45 243 288 9 5 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 44 243 288 (Polychromatic418967fa.accept_13_5_9_2_1_1489 44 243
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 243 288
  (Polychromatic418967fa.accept_11_10_1_2_1_1624 43 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 243 288 3 14 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 243 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 41 243 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 243 288 (Polychromatic418967fa.accept_13_1_9_2_1_1448
  40 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 39 243 288 3 13 81 96
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 38 243 288
  (Polychromatic418967fa.accept_7_3_5_1_1_72 38 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 243 288 (Polychromatic418967fa.accept_13_11_9_2_1_2969 37 243 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 243 288 9 4 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 243 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165
  35 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 243 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 34 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 33 243 288 3 11 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 32 243 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 32 243 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 243 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 31
  243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 243 288 3 10 81 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 243 288
  (Polychromatic418967fa.accept_13_3_9_2_1_1486 29 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 243 288 (Polychromatic418967fa.accept_17_11_5_16_1_5600 28 243 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 27 243 288 9 3 27 32 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 26 243 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 26 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 243 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 25 243 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 243 288 3 8 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 243 288
  (Polychromatic418967fa.accept_25_23_18_13_1_17801 23 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 243 288 (Polychromatic418967fa.accept_21_1_12_15_1_2880 22 243 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 21 243 288 3 7 81 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 20 243 288
  (Polychromatic418967fa.accept_7_6_5_1_1_416 20 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 243 288 (Polychromatic418967fa.accept_13_6_9_2_1_838 19 243 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 243 288 9 2 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 243 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 17
  243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 243 288
  (Polychromatic418967fa.accept_10_6_3_8_1_1660 16 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 15 243 288 3 5 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 14 243 288 (Polychromatic418967fa.accept_11_3_1_2_1_1063 14 243 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 243 288 (Polychromatic418967fa.accept_7_6_5_1_1_416 13 243 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 243 288 3 4 81 96 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 243 288
  (Polychromatic418967fa.accept_7_4_5_1_1_418 11 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 243 288 (Polychromatic418967fa.accept_7_3_5_1_1_72 10 243 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 9 243 288 9 1 27 32 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 8 243 288 (Polychromatic418967fa.accept_19_8_15_3_1_5546 8 243 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 243 288
  (Polychromatic418967fa.accept_13_7_9_2_1_2167 7 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 243 288 3 2 81 96 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 243 288 (Polychromatic418967fa.accept_10_5_3_8_1_1165 5 243 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 243 288 (Polychromatic418967fa.accept_7_4_5_1_1_418 4 243 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 3 243 288 3 1 81 96 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 2 243 288
  (Polychromatic418967fa.accept_17_2_5_16_1_1264 2 243 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 243 288 (Polychromatic418967fa.accept_10_1_3_8_1_136 1 243 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 243 288)))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 47 242 288
  (Eq.refl Bool.true) (allA_succ_of_gcd 46 242 288 2 23 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 242 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 45 242 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 242 288 2 22 121 144 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 242 288 (accept_3_4 43
  242 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 242 288 2 21 121 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 242 288
  (Polychromatic418967fa.accept_26_15_8_2_1_17820 41 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 242 288 2 20 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 242 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 39 242 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 242 288 2 19 121 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 242 288 (accept_3_4 37 242 288
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 242 288 2 18 121 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 242 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 35 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 242 288 2 17 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 242 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 33 242 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 242 288 2 16 121 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 242 288 (accept_3_4 31 242 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 242 288 2 15 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 242 288 (Polychromatic418967fa.accept_15_14_2_3_1_1980
  29 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 242 288 2 14 121 144
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 242 288
  (Polychromatic418967fa.accept_15_12_2_3_1_1146 27 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 242 288 2 13 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 242 288 (accept_3_4 25 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 242 288 2 12 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 242 288 (Polychromatic418967fa.accept_13_10_8_2_1_3829 23 242 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 242 288 2 11 121 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 242 288
  (Polychromatic418967fa.accept_25_21_17_13_1_17848 21 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 242 288 2 10 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 242 288 (accept_3_4 19 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 242 288 2 9 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 242 288 (Polychromatic418967fa.accept_7_3_4_1_1_71 17 242 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 242 288 2 8 121 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 242 288
  (Polychromatic418967fa.accept_10_5_2_8_1_135 15 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 242 288 2 7 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 242 288 (accept_3_4 13 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 242 288 2 6 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 242 288 (Polychromatic418967fa.accept_14_11_4_8_1_664 11 242 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 242 288 2 5 121 144 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 242 288
  (Polychromatic418967fa.accept_19_9_14_3_1_2912 9 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 242 288 2 4 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 242 288 (accept_3_4 7 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 242 288 2 3 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 5 242 288 (Polychromatic418967fa.accept_7_5_4_1_1_412 5 242 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 242 288 2 2 121 144 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 242 288
  (Polychromatic418967fa.accept_7_3_4_1_1_71 3 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 242 288 2 1 121 144 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 1 242 288 (accept_3_4 1 242 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 242
  288))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 48 241 288 (Eq.refl Bool.true) (allA_succ_of_accept 47
  241 288 (accept_3_5 47 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 241 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 46 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 45 241 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 45 241 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 241 288 (accept_3_5 44 241 288 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 43 241 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 43 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 241 288
  (Polychromatic418967fa.accept_19_4_13_3_1_5571 42 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 41 241 288 (accept_3_5 41 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  40 241 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 40 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 39 241 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 39 241 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 241 288 (accept_3_5 38 241 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 37 241 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 37 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 241 288
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 36 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 35 241 288 (accept_3_5 35 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  34 241 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 34 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 33 241 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 33 241 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 241 288 (accept_3_5 32 241 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 31 241 288 (Polychromatic418967fa.accept_13_5_7_2_1_852 31 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 241 288
  (Polychromatic418967fa.accept_7_2_3_1_1_10 30 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 29 241 288 (accept_3_5 29 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  28 241 288 (Polychromatic418967fa.accept_15_13_1_3_1_1972 28 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 27 241 288 (Polychromatic418967fa.accept_19_8_13_3_1_4172 27 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 241 288 (accept_3_5 26 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 241 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 25 241 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 241 288
  (Polychromatic418967fa.accept_17_7_3_16_1_2208 24 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 23 241 288 (accept_3_5 23 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  22 241 288 (Polychromatic418967fa.accept_13_9_7_2_1_3869 22 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 21 241 288 (Polychromatic418967fa.accept_13_8_7_2_1_2988 21 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 241 288 (accept_3_5 20 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 241 288 (Polychromatic418967fa.accept_7_5_3_1_1_424 19 241 288
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 241 288
  (Polychromatic418967fa.accept_7_4_3_1_1_87 18 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 241 288 (accept_3_5 17 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  16 241 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 16 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 241 288 (Polychromatic418967fa.accept_23_15_11_12_1_17696 15 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 241 288 (accept_3_5 14 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 241 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 13 241
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 241 288
  (Polychromatic418967fa.accept_7_5_3_1_1_424 12 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 241 288 (accept_3_5 11 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  10 241 288 (Polychromatic418967fa.accept_19_10_13_3_1_13772 10 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 241 288 (Polychromatic418967fa.accept_7_2_3_1_1_10 9 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 241 288 (accept_3_5 8 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 241 288 (Polychromatic418967fa.accept_17_7_3_16_1_2208 7 241
  288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 241 288
  (Polychromatic418967fa.accept_15_6_1_3_1_2852 6 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 241 288 (accept_3_5 5 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4
  241 288 (Polychromatic418967fa.accept_7_4_3_1_1_87 4 241 288 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 241 288 (Polychromatic418967fa.accept_10_3_1_8_1_132 3 241 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 241 288 (accept_3_5 2 241 288 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 1 241 288 (Polychromatic418967fa.accept_11_1_10_2_1_58 1 241 288 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 241 288))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_288_segment_003)))))))))))))))))))))))))))))))))))))))))))))))


