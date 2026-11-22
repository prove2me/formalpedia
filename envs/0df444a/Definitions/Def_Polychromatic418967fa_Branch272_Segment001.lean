-- Prove2me | Definitions.Def_Polychromatic418967fa_Branch272_Segment001
-- name    : Polychromatic418967fa_Branch272_Segment001
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:53:00.104067+00:00
-- url     : https://prove2.me/theorems/16717919-5e30-46f5-8f61-8ef217f6d5e7
-- title:
--   Polychromatic branch proof segment
-- statement:
--   Checked segment of the pinned Polychromatic branch proof. Kernel types, definition values and allowed axioms match the original proof.
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Compute.lean

import Definitions.Def_Polychromatic418967fa_Helpers016
import Definitions.Def_Polychromatic418967fa_Branch272_Segment000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.defProp false

def Polychromatic418967fa.branch_272_segment_001 : allB 188 272 :=
  allB_succ' 86 187 272 (Eq.refl Bool.true) (allA_of_3_0 86 187 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ'
  87 186 272 (Eq.refl Bool.true) (allA_succ_of_gcd 86 186 272 2 43 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 186 272 (accept_3_2 85 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 84 186 272 2 42 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 186 272 (Polychromatic418967fa.accept_13_5_4_12_1_2058 83 186
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 186 272 2 41 93 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 186 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 186 272 2 40 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 186 272 (accept_3_2 79 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 186 272 2 39 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 186 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 186 272 2 38 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 186 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 186 272 2 37 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 186 272 (accept_3_2 73 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 186 272 2 36 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 186 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 186 272 2 35 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 186 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 186 272 2 34 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 186 272 (accept_3_2 67 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 186 272 2 33 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 186 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 186 272 2 32 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 186 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 186 272 2 31 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 186 272 (accept_3_2 61 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 186 272 2 30 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 186 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 186 272 2 29 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 186 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 186 272 2 28 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 186 272 (accept_3_2 55 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 186 272 2 27 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 186 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 186 272 2 26 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 186 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 186 272 2 25 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 186 272 (accept_3_2 49 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 186 272 2 24 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 186 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 186 272 2 23 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 186 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 186 272 2 22 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 186 272 (accept_3_2 43 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 186 272 2 21 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 186 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 186 272 2 20 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 186 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 186 272 2 19 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 186 272 (accept_3_2 37 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 186 272 2 18 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 186 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 186 272 2 17 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 186 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 186 272 2 16 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 186 272 (accept_3_2 31 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 186 272 2 15 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 186 272 (Polychromatic418967fa.accept_13_3_4_12_1_36 29 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 186 272 2 14 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 186 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 186 272 2 13 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 186 272 (accept_3_2 25 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 186 272 2 12 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 186 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 186 272 2 11 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 186 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 186 272 2 10 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 186 272 (accept_3_2 19 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 186 272 2 9 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 186 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 186 272 2 8 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 186 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 186 272 2 7 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 186 272 (accept_3_2 13 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 186 272 2 6 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 186 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 186 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 186 272 2 5 93 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 186 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 186 272 2 4 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 186 272 (accept_3_2 7 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 186
  272 2 3 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  186 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 186 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 186 272 2 2 93 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 186 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 186 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 186 272 2 1 93 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 186 272 (accept_3_2 1 186 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 186
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 88 185 272
  (Eq.refl Bool.true) (allA_succ_of_accept 87 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 185 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 86 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 185 272 (accept_3_2 85 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 185 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 185 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 83 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 185 272 (accept_3_2 82 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 185 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 80 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 185 272 (accept_3_2 79 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 185 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 78 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 185 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 77 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 185 272 (accept_3_2 76 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 185 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 185 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 185 272 (accept_3_2 73 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 185 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 185 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 185 272 (accept_3_2 70 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 185 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 68 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 185 272 (accept_3_2 67 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 185 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 185 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 185 272 (accept_3_2 64 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 185 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 62 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 185 272 (accept_3_2 61 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 185 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 185 272 (Polychromatic418967fa.accept_15_14_5_2_1_4761 59 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 185 272 (accept_3_2 58 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 185 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 185 272
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 56 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 185 272 (accept_3_2 55 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 185 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 54 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 185 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 185 272 (accept_3_2 52 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 185 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 185 272 (accept_3_2 49 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 185 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 185 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 47 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 185 272 (accept_3_2 46 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 185 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 185 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 185 272 (accept_3_2 43 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 185 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 185 272 (Polychromatic418967fa.accept_13_2_3_12_1_735 41 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 185 272 (accept_3_2 40 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 185 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 185 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 185 272 (accept_3_2 37 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 185 272 (Polychromatic418967fa.accept_24_12_17_8_1_16702 36 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 35 185 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 185 272 (accept_3_2 34 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 185 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 185 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 185 272 (accept_3_2 31 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 185 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 185 272 (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 185 272 (accept_3_2 28 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 185 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 185 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 26 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 185 272 (accept_3_2 25 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 185 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 185 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 185 272 (accept_3_2 22 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 185 272
  (Polychromatic418967fa.accept_19_1_14_6_1_1983 20 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 185 272 (accept_3_2 19 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 185 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 185 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 185 272 (accept_3_2 16 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 185 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 185 272 (accept_3_2 13 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 185 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 185 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 185 272 (accept_3_2 10 185 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 185 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 185 272 (accept_3_2 7 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  185 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 185 272 (Polychromatic418967fa.accept_19_5_14_6_1_4413 5 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 185 272 (accept_3_2 4 185 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3 185 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 185 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 185 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 185 272 (accept_3_2 1 185 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 185
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 89 184 272
  (Eq.refl Bool.true) (allA_of_3_0 89 184 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 90 183 272 (Eq.refl
  Bool.true) (allA_succ_of_accept 89 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 183 272 (accept_3_2 88 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 183 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 183 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 183 272 (accept_3_2 85 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 183 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 84 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 183 272 (accept_3_2 82 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 183 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 183 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 80 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 183 272 (accept_3_2 79 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 183 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 183 272 (accept_3_2 76 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 183 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 183 272
  (Polychromatic418967fa.accept_15_14_3_2_1_2811 74 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 183 272 (accept_3_2 73 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 183 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 183 272 (accept_3_2 70 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 183 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 183 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 183 272 (accept_3_2 67 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 183 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 183 272 (accept_3_2 64 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 183 272 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 183 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 183 272
  (Polychromatic418967fa.accept_9_8_3_2_1_417 62 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 183 272 (accept_3_2 61 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 183 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 183 272 (accept_3_2 58 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 183 272 (Polychromatic418967fa.accept_13_5_1_12_1_740 57 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 183 272
  (Polychromatic418967fa.accept_19_18_12_6_1_7187 56 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 183 272 (accept_3_2 55 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 183 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 183 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 183 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 183 272 (accept_3_2 52 183 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 183 272 (Polychromatic418967fa.accept_7_2_1_6_1_173
  51 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 183 272
  (Polychromatic418967fa.accept_9_5_3_2_1_171 50 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 183 272 (accept_3_2 49 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 183 272 (Polychromatic418967fa.accept_11_4_7_8_1_1926 48 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 183 272 (accept_3_2 46 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 183 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 45 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 183 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 183 272 (accept_3_2 43 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 183 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 183 272 (accept_3_2 40 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 183 272 (Polychromatic418967fa.accept_21_18_15_20_1_6076 39 183 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 183 272
  (Polychromatic418967fa.accept_22_16_7_8_1_15092 38 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 37 183 272 (accept_3_2 37 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 36 183 272 (Polychromatic418967fa.accept_19_17_12_6_1_8650 36 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35
  183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 183 272 (accept_3_2 34
  183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 183 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 32 183 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 183 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 183 272 (accept_3_2 31 183 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 30 183 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29
  183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 183 272 (accept_3_2 28
  183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 183 272
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 183 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 183 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 183 272 (accept_3_2 25 183 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 183 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 183 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23
  183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 183 272 (accept_3_2 22
  183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 183 272
  (Polychromatic418967fa.accept_10_1_3_2_1_220 21 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 20 183 272 (Polychromatic418967fa.accept_15_5_3_2_1_5930 20 183 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 183 272 (accept_3_2 19 183 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 18 183 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 183 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 183 272 (accept_3_2 16 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 183 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 183 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 183 272 (accept_3_2 13 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 183 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 183 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 183 272 (accept_3_2 10 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  183 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 183 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 183 272 (accept_3_2 7 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 183 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 183 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 183 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 183 272 (accept_3_2 4 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  183 272 (Polychromatic418967fa.accept_23_3_22_19_1_10170 3 183 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 183 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 183 272 (accept_3_2 1 183 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 183
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 91 182 272
  (Eq.refl Bool.true) (allA_succ_of_gcd 90 182 272 2 45 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 182 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 182 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 182 272 2 44 91 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 182 272
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 87 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 182 272 2 43 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 182 272 (accept_3_2 85 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 182 272 2 42 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 182 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 182 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 182 272 2 41 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 182 272
  (Polychromatic418967fa.accept_19_5_11_6_1_1909 81 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 182 272 2 40 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 182 272 (accept_3_2 79 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 182 272 2 39 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 182 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 182 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 182 272 2 38 91 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 182 272
  (Polychromatic418967fa.accept_19_18_11_6_1_5768 75 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 182 272 2 37 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 182 272 (accept_3_2 73 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 182 272 2 36 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 182 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 71 182 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 182 272 2 35 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 182 272
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 69 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 182 272 2 34 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 182 272 (accept_3_2 67 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 182 272 2 33 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 182 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 182 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 182 272 2 32 91 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 182 272
  (Polychromatic418967fa.accept_22_19_6_8_1_10580 63 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 182 272 2 31 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 182 272 (accept_3_2 61 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 182 272 2 30 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 182 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 182 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 182 272 2 29 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 182 272
  (Polychromatic418967fa.accept_20_17_2_12_1_8168 57 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 182 272 2 28 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 182 272 (accept_3_2 55 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 182 272 2 27 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 182 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 182 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 182 272 2 26 91 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 182 272
  (Polychromatic418967fa.accept_19_13_11_6_1_3128 51 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 182 272 2 25 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 182 272 (accept_3_2 49 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 182 272 2 24 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 182 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 182 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 182 272 2 23 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 182 272
  (Polychromatic418967fa.accept_24_21_14_8_1_13333 45 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 182 272 2 22 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 182 272 (accept_3_2 43 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 182 272 2 21 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 182 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 182 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 182 272 2 20 91 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 182 272
  (Polychromatic418967fa.accept_19_1_11_6_1_7152 39 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 182 272 2 19 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 182 272 (accept_3_2 37 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 182 272 2 18 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 182 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 182 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 182 272 2 17 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 182 272
  (Polychromatic418967fa.accept_19_14_11_6_1_7151 33 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 182 272 2 16 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 182 272 (accept_3_2 31 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 182 272 2 15 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 182 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 182 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 182 272 2 14 91 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 182 272
  (Polychromatic418967fa.accept_20_7_2_12_1_6642 27 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 182 272 2 13 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 182 272 (accept_3_2 25 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 182 272 2 12 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 182 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 182 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 182 272 2 11 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 182 272
  (Polychromatic418967fa.accept_24_21_14_8_1_13333 21 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 182 272 2 10 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 182 272 (accept_3_2 19 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 182 272 2 9 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 182 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 17 182 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 182 272 2 8 91 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 182 272
  (Polychromatic418967fa.accept_19_15_11_6_1_11404 15 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 182 272 2 7 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 182 272 (accept_3_2 13 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 182 272 2 6 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 182 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 182 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 182 272 2 5 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 182 272
  (Polychromatic418967fa.accept_20_9_2_12_1_5144 9 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 182 272 2 4 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 182 272 (accept_3_2 7 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 182
  272 2 3 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  182 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 5 182 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 182 272 2 2 91 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 182 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 182 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 182 272 2 1 91 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 182 272 (accept_3_2 1 182 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 182
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 92 181 272
  (Eq.refl Bool.true) (allA_of_3_0 92 181 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 93 180 272 (Eq.refl
  Bool.true) (allA_succ_of_gcd 92 180 272 4 23 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 91 180 272 (accept_3_2 91 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 180 272 2 45 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 180 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 89 180 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 180 272 4 22 45 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 180 272
  (Polychromatic418967fa.accept_21_3_12_20_1_1891 87 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 180 272 2 43 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 180 272 (accept_3_2 85 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 180 272 4 21 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 180 272 (Polychromatic418967fa.accept_14_13_12_6_1_2735 83 180 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 180 272 2 41 90 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 180 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 180 272 4 20 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 180 272 (accept_3_2 79 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 180 272 2 39 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 180 272 (Polychromatic418967fa.accept_24_5_12_8_1_16700 77 180 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 180 272 4 19 45 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 180 272
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 75 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 180 272 2 37 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 180 272 (accept_3_2 73 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 180 272 4 18 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 180 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 180 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 180 272 2 35 90 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 180 272
  (Polychromatic418967fa.accept_13_4_11_12_1_1318 69 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 180 272 4 17 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 180 272 (accept_3_2 67 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 180 272 2 33 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 180 272 (Polychromatic418967fa.accept_22_21_4_8_1_12043 65 180 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 180 272 4 16 45 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 180 272
  (Polychromatic418967fa.accept_27_9_18_2_1_16701 63 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 180 272 2 31 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 180 272 (accept_3_2 61 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 180 272 4 15 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 180 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 59 180 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 180 272 2 29 90 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 180 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 180 272 4 14 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 180 272 (accept_3_2 55 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 180 272 2 27 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 180 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 180 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 180 272 4 13 45 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 180 272
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 51 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 180 272 2 25 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 180 272 (accept_3_2 49 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 180 272 4 12 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 180 272 (Polychromatic418967fa.accept_24_23_12_8_1_16677 47 180 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 180 272 2 23 90 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 180 272
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 45 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 180 272 4 11 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 180 272 (accept_3_2 43 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 180 272 2 21 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 180 272 (Polychromatic418967fa.accept_14_13_12_6_1_2735 41 180 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 180 272 4 10 45 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 180 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 180 272 2 19 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 180 272 (accept_3_2 37 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 180 272 4 9 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 180 272 (Polychromatic418967fa.accept_19_16_9_6_1_5799 35 180 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 180 272 2 17 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 180 272
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 180 272 4 8 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 180 272 (accept_3_2 31 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 180 272 2 15 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 180 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 180 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 180 272 4 7 45 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 180 272
  (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 180 272 2 13 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 180 272 (accept_3_2 25 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 180 272 4 6 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 180 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 23 180 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 180 272 2 11 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 180 272
  (Polychromatic418967fa.accept_22_21_4_8_1_12043 21 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 20 180 272 4 5 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 19 180 272 (accept_3_2 19 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 180 272 2 9 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 180 272 (Polychromatic418967fa.accept_13_4_11_12_1_1318 17 180 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 180 272 4 4 45 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 180 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 180 272 2 7 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 180 272 (accept_3_2 13 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 180 272 4 3 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 180 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 180 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 180 272 2 5 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 180 272
  (Polychromatic418967fa.accept_21_9_12_20_1_10792 9 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 8 180 272 4 2 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 7 180 272 (accept_3_2 7 180 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 6 180 272 2 3 90 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 5 180 272 (Polychromatic418967fa.accept_24_5_12_8_1_16700 5 180 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 180 272 4 1 45 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 180 272 (Polychromatic418967fa.accept_19_3_9_6_1_12696 3 180 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 180 272 2 1 90 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 180 272 (accept_3_2 1
  180 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 180
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 94 179
  272 (Eq.refl Bool.true) (allA_succ_of_accept 93 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 179 272
  (Polychromatic418967fa.accept_19_16_8_6_1_4407 92 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 179 272 (accept_3_2 91 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 179 272 (Polychromatic418967fa.accept_19_14_8_6_1_981 90 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 179 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 179 272 (accept_3_2 88 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 179 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 86 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 179 272 (accept_3_2 85 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 179 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 179 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 83 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 179 272 (accept_3_2 82 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 179 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 179 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 80 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 179 272 (accept_3_2 79 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 179 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 179 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 179 272 (accept_3_2 76 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 179 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 179 272 (accept_3_2 73 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 179 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 179 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 71 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 179 272 (accept_3_2 70 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 179 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 68 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 179 272 (accept_3_2 67 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 179 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 179 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 179 272 (accept_3_2 64 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 179 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 179 272 (accept_3_2 61 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 179 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 179 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 179 272 (accept_3_2 58 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 179 272
  (Polychromatic418967fa.accept_21_14_11_20_1_12301 56 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 179 272 (accept_3_2 55 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 179 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 179 272 (Polychromatic418967fa.accept_20_13_19_12_1_5143 53
  179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 179 272 (accept_3_2 52
  179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 179 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 51 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 50 179 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 50 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 179 272 (accept_3_2 49 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 48 179 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 179 272 (Polychromatic418967fa.accept_7_5_4_6_1_167
  47 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 179 272 (accept_3_2 46
  179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 179 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 45 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 179 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 179 272 (accept_3_2 43 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 179 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 179 272 (Polychromatic418967fa.accept_9_5_8_2_1_409
  41 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 179 272 (accept_3_2 40
  179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 179 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 39 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 38 179 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 179 272 (accept_3_2 37 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 36 179 272 (Polychromatic418967fa.accept_19_17_8_6_1_7146 36 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 179 272
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 35 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 34 179 272 (accept_3_2 34 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 33 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 179 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 32 179 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 179 272 (accept_3_2 31 179 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 30 179 272 (Polychromatic418967fa.accept_7_2_4_6_1_166
  30 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 179 272
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 29 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 28 179 272 (accept_3_2 28 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 27 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 179 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 179 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 179 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 179 272 (accept_3_2 25 179 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 179 272 (Polychromatic418967fa.accept_7_3_4_6_1_329
  24 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 179 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 179 272 (accept_3_2 22 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 179 272 (Polychromatic418967fa.accept_13_7_10_12_1_2047 20 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 179 272 (accept_3_2 19 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 179 272 (Polychromatic418967fa.accept_15_3_14_2_1_1888 18 179
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 179 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 179 272 (accept_3_2 16 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 179 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 14 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 179 272 (accept_3_2 13 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 179 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 179 272
  (Polychromatic418967fa.accept_10_1_9_2_1_45 11 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 179 272 (accept_3_2 10 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 179 272 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 179 272 (accept_3_2 7 179 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 179 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 179 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 179 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 5 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 179 272 (accept_3_2 4 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  179 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 179 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 179 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 179 272 (accept_3_2 1 179 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 179
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 95 178
  272 (Eq.refl Bool.true) (allA_of_3_0 95 178 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 96 177 272
  (Eq.refl Bool.true) (allA_succ_of_accept 95 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 177 272 (accept_3_2 94 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 177 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 177 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 177 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 92 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 177 272 (accept_3_2 91 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 177 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 177 272 (accept_3_2 88 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 177 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 177 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 86 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 177 272 (accept_3_2 85 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 177 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 177 272 (accept_3_2 82 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 177 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 177 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 80 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 177 272 (accept_3_2 79 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 177 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 177 272 (accept_3_2 76 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 177 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 177 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 74 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 177 272 (accept_3_2 73 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 177 272 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 177 272 (accept_3_2 70 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 177 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 69 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 177 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 68 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 177 272 (accept_3_2 67 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 177 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 177 272 (accept_3_2 64 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 177 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 63 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 177 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 62 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 177 272 (accept_3_2 61 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 177 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 177 272 (accept_3_2 58 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 177 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 177 272
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 56 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 177 272 (accept_3_2 55 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 177 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 53 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 177 272 (accept_3_2 52 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 177 272 (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 177 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 177 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 50 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 177 272 (accept_3_2 49 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 177 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 177 272 (accept_3_2 46 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 177 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 177 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 44 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 177 272 (accept_3_2 43 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 177 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 41 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 177 272 (accept_3_2 40 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 177 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 177 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 38 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 177 272 (accept_3_2 37 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 177 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 35 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 177 272 (accept_3_2 34 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 177 272 (Polychromatic418967fa.accept_13_7_8_12_1_2810 33 177 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 177 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 32 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 177 272 (accept_3_2 31 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 177 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 177 272 (accept_3_2 28 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 27 177 272 (Polychromatic418967fa.accept_13_1_8_12_1_2045 27 177 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 177 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 26 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 177 272 (accept_3_2 25 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 177 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 23 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 177 272 (accept_3_2 22 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 177 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 177 272
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 177 272 (accept_3_2 19 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 177 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 17 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 177 272 (accept_3_2 16 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 177 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 177 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 14 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 177 272 (accept_3_2 13 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 177 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 11 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 177 272 (accept_3_2 10 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 177 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 177 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 8 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 177 272 (accept_3_2 7 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  177 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 177 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 5 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 177 272 (accept_3_2 4 177 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 177 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 177 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 177 272
  (Polychromatic418967fa.accept_20_2_17_12_1_5178 2 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 177 272 (accept_3_2 1 177 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 177
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 97 176
  272 (Eq.refl Bool.true) (allA_succ_of_gcd 96 176 272 16 6 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 176 272 (Polychromatic418967fa.accept_13_4_7_12_1_2823 95 176
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 176 272 2 47 88 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 176 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 176 272 4 23 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 176 272 (accept_3_2 91 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 176 272 2 45 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 176 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 176 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 176 272 8 11 22 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 176 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 176 272 2 43 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 176 272 (accept_3_2 85 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 176 272 4 21 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 176 272 (Polychromatic418967fa.accept_13_5_7_12_1_2757 83 176 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 176 272 2 41 88 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 176 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 176 272 16 5 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 176 272 (accept_3_2 79 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 176 272 2 39 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 176 272 (Polychromatic418967fa.accept_14_7_8_6_1_1164 77 176 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 176 272 4 19 44 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 176 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 176 272 2 37 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 176 272 (accept_3_2 73 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 176 272 8 9 22 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 176 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 176 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 176 272 2 35 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 176 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 69
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 176 272 4 17 44 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 176 272 (accept_3_2 67
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 176 272 2 33 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 176 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 65 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 176 272 16 4 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 63 176 272 (Polychromatic418967fa.accept_13_11_7_12_1_2758 63 176 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 176 272 2 31 88 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 176 272 (accept_3_2 61 176 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 176 272 4 15 44 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 176 272
  (Polychromatic418967fa.accept_21_17_8_20_1_7805 59 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 58 176 272 2 29 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 57 176 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 57 176 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 176 272 8 7 22 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 176 272 (accept_3_2 55 176 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 176 272 2 27 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 176 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 52 176 272 4 13 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 51 176 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 176 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 176 272 2 25 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 176 272 (accept_3_2 49 176 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 176 272 16 3 11 17 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 176 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 176 272 2 23 88 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 176 272
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 45 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 176 272 4 11 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 176 272 (accept_3_2 43 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 176 272 2 21 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 176 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 176 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 176 272 8 5 22 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 176 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 176 272 2 19 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 176 272 (accept_3_2 37 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 176 272 4 9 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 176 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 176 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 176 272 2 17 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 176 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 33
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 176 272 16 2 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 176 272 (accept_3_2 31
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 176 272 2 15 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 176 272
  (Polychromatic418967fa.accept_18_11_14_2_1_5058 29 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 176 272 4 7 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 176 272 (Polychromatic418967fa.accept_23_4_15_19_1_10311 27 176 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 176 272 2 13 88 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 176 272 (accept_3_2 25
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 176 272 8 3 22 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 176 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 176 272 2 11 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 176 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 21 176 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 176 272 4 5 44 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 176 272 (accept_3_2 19 176 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 176 272 2 9 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 176 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 176 272 16 1 11 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 176 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 176 272 2 7 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 176 272 (accept_3_2 13 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 176 272 4 3 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 176 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 176 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 176 272 2 5 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 176 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 176 272 8 1 22 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 176 272 (accept_3_2 7
  176 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 176 272 2 3 88 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 176 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 176 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 4 176 272 4 1 44 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 3 176 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 3 176 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 176 272 2 1 88 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 176 272 (accept_3_2 1 176 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 176
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 98
  175 272 (Eq.refl Bool.true) (allA_of_3_0 98 175 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 99 174 272
  (Eq.refl Bool.true) (allA_succ_of_gcd 98 174 272 2 49 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 174 272 (accept_3_2 97 174 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 96 174 272 2 48 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 95 174 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 95 174 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 174 272 2 47 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 174 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 174 272 2 46 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 174 272 (accept_3_2 91 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 174 272 2 45 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 174 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 174 272 2 44 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 174 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 87 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 174 272 2 43 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 174 272 (accept_3_2 85 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 174 272 2 42 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 174 272 (Polychromatic418967fa.accept_15_8_9_2_1_1897 83 174 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 174 272 2 41 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 174 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 174 272 2 40 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 174 272 (accept_3_2 79 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 174 272 2 39 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 174 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 174 272 2 38 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 174 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 174 272 2 37 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 174 272 (accept_3_2 73 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 174 272 2 36 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 174 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 71 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 174 272 2 35 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 174 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 174 272 2 34 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 174 272 (accept_3_2 67 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 174 272 2 33 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 174 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 174 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 174 272 2 32 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 174 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 174 272 2 31 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 174 272 (accept_3_2 61 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 174 272 2 30 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 174 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 174 272 2 29 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 174 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 174 272 2 28 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 174 272 (accept_3_2 55 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 174 272 2 27 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 174 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 53 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 174 272 2 26 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 174 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 174 272 2 25 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 174 272 (accept_3_2 49 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 174 272 2 24 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 174 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 174 272 2 23 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 174 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 174 272 2 22 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 174 272 (accept_3_2 43 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 174 272 2 21 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 174 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 174 272 2 20 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 174 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 174 272 2 19 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 174 272 (accept_3_2 37 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 174 272 2 18 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 174 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 174 272 2 17 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 174 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 174 272 2 16 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 174 272 (accept_3_2 31 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 174 272 2 15 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 174 272 (Polychromatic418967fa.accept_23_6_13_19_1_10304 29 174 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 174 272 2 14 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 174 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 174 272 2 13 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 174 272 (accept_3_2 25 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 174 272 2 12 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 174 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 174 272 2 11 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 174 272
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 21 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 174 272 2 10 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 174 272 (accept_3_2 19 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 174 272 2 9 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 174 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 174 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 174 272 2 8 87 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 174 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 15 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 174 272 2 7 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 174 272 (accept_3_2 13 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 174 272 2 6 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 174 272 (Polychromatic418967fa.accept_15_11_9_2_1_4780 11 174 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 174 272 2 5 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 174 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 174 272 2 4 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 174 272 (accept_3_2 7 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 174
  272 2 3 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  174 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 174 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 174 272 2 2 87 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 174 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 174 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 174 272 2 1 87 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 174 272 (accept_3_2 1 174 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 174
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ' 100
  173 272 (Eq.refl Bool.true) (allA_succ_of_accept 99 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 173 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 173 272 (accept_3_2 97 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 173 272 (Polychromatic418967fa.accept_13_5_4_12_1_2058 96 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 173 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 173 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 173 272 (accept_3_2 94 173 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 173 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 92 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 173 272 (accept_3_2 91 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 173 272 (Polychromatic418967fa.accept_20_10_13_12_1_9726 90 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 89 173 272 (Polychromatic418967fa.accept_13_11_4_12_1_3585 89 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 173 272 (accept_3_2 88 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87
  173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 173 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 86 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 173 272 (accept_3_2 85 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 173 272 (Polychromatic418967fa.accept_15_9_8_2_1_1109 84 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 173 272 (Polychromatic418967fa.accept_13_5_4_12_1_2058 83 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 173 272 (accept_3_2 82 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 173 272
  (Polychromatic418967fa.accept_13_2_4_12_1_745 80 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 173 272 (accept_3_2 79 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 173 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 173 272 (Polychromatic418967fa.accept_19_1_2_6_1_4411 77 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 173 272 (accept_3_2 76 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 173 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 74 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 173 272 (accept_3_2 73 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 173 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 173 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 173 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 173 272 (accept_3_2 70 173 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 173 272
  (Polychromatic418967fa.accept_13_3_4_12_1_36 68 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 173 272 (accept_3_2 67 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 173 272 (Polychromatic418967fa.accept_15_6_8_2_1_104 66 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 173 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 65 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 173 272 (accept_3_2 64 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 173 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 173 272 (accept_3_2 61 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 173 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 173 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341 59 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 173 272 (accept_3_2 58 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 173 272
  (Polychromatic418967fa.accept_21_14_5_20_1_12299 56 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 173 272 (accept_3_2 55 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 173 272 (Polychromatic418967fa.accept_13_2_4_12_1_745 54 173 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 173 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 173 272 (accept_3_2 52 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 173 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 50 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 173 272 (accept_3_2 49 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 173 272 (Polychromatic418967fa.accept_19_10_2_6_1_5731 48 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 173 272 (Polychromatic418967fa.accept_13_8_4_12_1_2753 47 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 173 272 (accept_3_2 46 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 173 272
  (Polychromatic418967fa.accept_13_5_4_12_1_2058 44 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 173 272 (accept_3_2 43 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 173 272 (Polychromatic418967fa.accept_13_3_4_12_1_36 42 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 173 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 41 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 173 272 (accept_3_2 40 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 173 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 173 272 (accept_3_2 37 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 173 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 173 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 173 272 (accept_3_2 34 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 173 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 32 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 173 272 (accept_3_2 31 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 173 272 (Polychromatic418967fa.accept_20_10_13_12_1_9726 30 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 29 173 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 173 272 (accept_3_2 28 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 173 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 173 272 (accept_3_2 25 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 173 272 (Polychromatic418967fa.accept_13_11_4_12_1_3585 24 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 173 272 (Polychromatic418967fa.accept_19_4_2_6_1_7181 23 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 173 272 (accept_3_2 22 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 21 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 173 272
  (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 173 272 (accept_3_2 19 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 173 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 173 272 (Polychromatic418967fa.accept_18_17_11_2_1_7782 17 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 173 272 (accept_3_2 16 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 173 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 173 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 14 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 173 272 (accept_3_2 13 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 173 272 (Polychromatic418967fa.accept_19_12_2_6_1_9981 12 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 173 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 173 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 173 272 (accept_3_2 10 173 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 173 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 8 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 173 272 (accept_3_2 7 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  173 272 (Polychromatic418967fa.accept_15_6_8_2_1_104 6 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 173 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 5 173 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 173 272 (accept_3_2 4 173 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 173 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 173 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 173 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 173 272 (accept_3_2 1 173 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 173
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  101 172 272 (Eq.refl Bool.true) (allA_of_3_0 101 172 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 102 171
  272 (Eq.refl Bool.true) (allA_succ_of_accept 101 171 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 171 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 171 272 (accept_3_2 100 171 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 171 272 (Polychromatic418967fa.accept_10_9_1_2_1_522
  99 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 171 272
  (Polychromatic418967fa.accept_15_8_6_2_1_1128 98 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 171 272 (accept_3_2 97 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 171 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 96 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 171 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 95 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 171 272 (accept_3_2 94 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 171 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 171 272
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 92 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 171 272 (accept_3_2 91 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 171 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 171 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 89 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 171 272 (accept_3_2 88 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 171 272 (Polychromatic418967fa.accept_15_12_6_2_1_2760 87 171 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 171 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 86 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 171 272 (accept_3_2 85 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 171 272 (Polychromatic418967fa.accept_13_6_2_12_1_2802 84 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 171 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 171 272 (accept_3_2 82 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 171 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 171 272
  (Polychromatic418967fa.accept_11_3_6_8_1_1924 80 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 171 272 (accept_3_2 79 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 171 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 171 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 171 272 (accept_3_2 76 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 171 272 (Polychromatic418967fa.accept_13_10_2_12_1_1332 75 171 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 171 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 74 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 171 272 (accept_3_2 73 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 171 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 171 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 171 272 (accept_3_2 70 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 171 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 69 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 171 272
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 68 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 171 272 (accept_3_2 67 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 171 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 66 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 171 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 171 272 (accept_3_2 64 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 171 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 171 272
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 62 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 61 171 272 (accept_3_2 61 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 60 171 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 171 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 171 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 59 171 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 171 272 (accept_3_2 58 171 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 171 272
  (Polychromatic418967fa.accept_13_5_2_12_1_1301 57 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 171 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 171 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 171 272 (accept_3_2 55 171 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 171 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 171 272 (accept_3_2 52 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 171 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 171 272 (Polychromatic418967fa.accept_22_6_17_8_1_10592 50 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 171 272 (accept_3_2 49 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 171 272 (Polychromatic418967fa.accept_21_6_3_20_1_6053 48 171
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 171 272 (accept_3_2 46 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 171 272 (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 171 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 171 272 (accept_3_2 43 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 171 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 171 272 (accept_3_2 40 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 171 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 171 272 (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 171 272 (accept_3_2 37 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 171 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 171
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 171 272 (accept_3_2 34 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 171 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 33 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 171 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 171 272 (accept_3_2 31 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 171 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 171 272 (accept_3_2 28 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 171 272 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 171 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 26 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 171 272 (accept_3_2 25 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 171 272 (Polychromatic418967fa.accept_14_10_3_6_1_2728 24 171
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 171 272 (accept_3_2 22 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 171 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 21 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 171 272 (Polychromatic418967fa.accept_23_20_10_19_1_16699 20 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 171 272 (accept_3_2 19 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 171 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 171 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 171 272 (accept_3_2 16 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 171 272 (Polychromatic418967fa.accept_22_15_17_8_1_16676 15 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 171 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 14 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 171 272 (accept_3_2 13 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 171 272 (Polychromatic418967fa.accept_15_12_6_2_1_2760 12 171
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 171 272 (accept_3_2 10 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  171 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 171 272 (Polychromatic418967fa.accept_15_8_6_2_1_1128 8 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 171 272 (accept_3_2 7 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 171 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 171 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 171 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 171 272 (accept_3_2 4 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  171 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 3 171 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 171 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 171 272 (accept_3_2 1 171 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 171
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  103 170 272 (Eq.refl Bool.true) (allA_succ_of_gcd 102 170 272 34 3 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 170 272 (Polychromatic418967fa.accept_7_3_2_6_1_56
  101 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 170 272 2 50 85 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 170 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 99 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 170 272 2 49 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 170 272 (accept_3_2 97 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 170 272 2 48 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 170 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 170 272 2 47 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 170 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 93 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 170 272 2 46 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 170 272 (accept_3_2 91 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 170 272 2 45 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 170 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 89 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 170 272 2 44 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 170 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 170 272 2 43 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_gcd 85 170 272 17 5 10 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_gcd 84 170 272 2 42 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 170 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 170
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 170 272 2 41 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 170 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 170 272 2 40 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 170 272 (accept_3_2 79 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 170 272 2 39 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 170 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 170 272 2 38 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 170 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 170 272 2 37 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 170 272 (accept_3_2 73 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 170 272 2 36 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 170 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 170 272 2 35 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 170 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 170 272 34 2 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 67 170 272 (accept_3_2 67 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66
  170 272 2 33 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 65 170 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 170 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 170 272 2 32 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 170 272 (Polychromatic418967fa.accept_13_11_1_12_1_742
  63 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 170 272 2 31 85 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 170 272
  (accept_3_2 61 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 170 272 2 30 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 170 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 58 170 272 2 29 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 57 170 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 56 170 272 2 28 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 55 170 272 (accept_3_2 55 170 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54 170 272 2 27 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 53 170 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53
  170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 170 272 2 26 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 51 170 272 17 3 10 16
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 50 170 272 2 25 85
  136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 170 272
  (accept_3_2 49 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 170 272 2 24 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 170 272
  (Polychromatic418967fa.accept_11_3_5_8_1_458 47 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 170 272 2 23 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 170 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 170 272 2 22 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 170 272 (accept_3_2 43 170 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 170 272 2 21 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 170 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41
  170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 170 272 2 20 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 170 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 170 272 2 19 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 170 272 (accept_3_2 37 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 170 272 2 18 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 170 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 170 272 34 1 5 8 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 170 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 33
  170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 170 272 2 16 85 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 170 272 (accept_3_2 31
  170 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 170 272 2 15 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 170 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 170 272 2 14 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 27 170 272 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 170 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 170 272 2 13 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 170 272 (accept_3_2 25 170 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 170 272 2 12 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 170 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 23 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 170 272 2 11 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 170 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 21 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 170 272 2 10 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 170 272 (accept_3_2 19 170 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 170 272 2 9 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 17 170 272 17 1 10 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_gcd 16 170 272 2 8 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 170 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 15 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 170 272 2 7 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 170 272 (accept_3_2 13 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 170 272 2 6 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 170 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 170 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 170 272 2 5 85 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 170 272
  (Polychromatic418967fa.accept_19_9_18_6_1_5778 9 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 170 272 2 4 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 170 272 (accept_3_2 7 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 170
  272 2 3 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  170 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 170 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 170 272 2 2 85 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 170 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 170 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 170 272 2 1 85 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 170 272 (accept_3_2 1 170 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 170
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (allB_succ'
  104 169 272 (Eq.refl Bool.true) (allA_of_3_0 104 169 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ' 105 168
  272 (Eq.refl Bool.true) (allA_succ_of_gcd 104 168 272 8 13 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 168 272 (accept_3_2 103 168 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 102 168 272 2 51 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 101 168 272 (Polychromatic418967fa.accept_27_20_6_2_1_16698 101 168 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 168 272 4 25 42 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 168 272
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 99 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 168 272 2 49 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 168 272 (accept_3_2 97 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 168 272 8 12 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 168 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 95 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 168 272 2 47 84 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 168 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 93 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 168 272 4 23 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 168 272 (accept_3_2 91 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 168 272 2 45 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 168 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 89 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 168 272 8 11 21 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 168 272
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 87 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 168 272 2 43 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 168 272 (accept_3_2 85 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 168 272 4 21 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 168 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 83 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 168 272 2 41 84 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 168 272
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 81 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 168 272 8 10 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 168 272 (accept_3_2 79 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 168 272 2 39 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 168 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 168 272 4 19 42 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 168 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 168 272 2 37 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 168 272 (accept_3_2 73 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 168 272 8 9 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 168 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 168 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 168 272 2 35 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 168 272
  (Polychromatic418967fa.accept_19_12_16_6_1_7175 69 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 168 272 4 17 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 168 272 (accept_3_2 67 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 168 272 2 33 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 168 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 168 272 8 8 21 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 168 272
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 63 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 168 272 2 31 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 168 272 (accept_3_2 61 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 168 272 4 15 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 168 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 168 272 2 29 84 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 168 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 168 272 8 7 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 168 272 (accept_3_2 55 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  168 272 2 27 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 168 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 168 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 168 272 4 13 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 168 272
  (Polychromatic418967fa.accept_27_24_6_2_1_12945 51 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 50 168 272 2 25 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 49 168 272 (accept_3_2 49 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 168 272 8 6 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 47 168 272 (Polychromatic418967fa.accept_19_9_16_6_1_5774 47 168 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 168 272 2 23 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 168 272 (Polychromatic418967fa.accept_10_5_8_2_1_517
  45 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 168 272 4 11 42 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 168 272
  (accept_3_2 43 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 168 272 2 21 84 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 168 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 41 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 168 272 8 5 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 168 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 168 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 168 272 2 19 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 168 272 (accept_3_2 37 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 168 272 4 9 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 168 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 168 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 168 272 2 17 84 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 168 272
  (Polychromatic418967fa.accept_22_11_14_8_1_12010 33 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 168 272 8 4 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 168 272 (accept_3_2 31 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 168 272 2 15 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 168 272 (Polychromatic418967fa.accept_15_14_3_2_1_2811 29 168 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 168 272 4 7 42 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 168 272
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 168 272 2 13 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 168 272 (accept_3_2 25 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 168 272 8 3 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 168 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 168 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 168 272 2 11 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 168 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21
  168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 168 272 4 5 42 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 168 272 (accept_3_2 19
  168 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 168 272 2 9 84 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 168 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 17 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 168 272 8 2 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 168 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 15 168 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 168 272 2 7 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 168 272 (accept_3_2 13 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 168 272 4 3 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 168 272 (Polychromatic418967fa.accept_19_11_16_6_1_7155 11 168
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 168 272 2 5 84 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 168 272
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 168 272 8 1 21 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 168 272 (accept_3_2 7 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 168
  272 2 3 84 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  168 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 168 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 168 272 4 1 42 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 168 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 168 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 168 272 2 1 84 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 168 272 (accept_3_2 1 168 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 168
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 106 167 272 (Eq.refl Bool.true) (allA_succ_of_accept 105 167 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 105 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 167 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 104 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 167 272 (accept_3_2 103 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 102 167 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 102 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 167 272
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 101 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 100 167 272 (accept_3_2 100 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 99 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 167 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 167 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 167 272 (accept_3_2 97 167 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 167 272 (Polychromatic418967fa.accept_9_6_5_2_1_421
  96 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 167 272
  (Polychromatic418967fa.accept_10_5_7_2_1_516 95 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 167 272 (accept_3_2 94 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 167 272 (Polychromatic418967fa.accept_13_1_11_12_1_1322 92 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 167 272 (accept_3_2 91 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 167 272 (Polychromatic418967fa.accept_22_2_13_8_1_13622 90 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 167 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 167 272 (accept_3_2 88 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 167 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 86 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 167 272 (accept_3_2 85 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 167 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 167 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 167 272
  (Polychromatic418967fa.accept_22_17_13_8_1_16697 83 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 167 272 (accept_3_2 82 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 167 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 167 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 167 272 (accept_3_2 79 167 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 167 272 (Polychromatic418967fa.accept_9_6_5_2_1_421
  78 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 167 272
  (Polychromatic418967fa.accept_14_7_13_6_1_1177 77 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 167 272 (accept_3_2 76 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 167 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 167 272 (accept_3_2 73 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 167 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 72 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 167 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 71 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 167 272 (accept_3_2 70 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 167 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 68 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 167 272 (accept_3_2 67 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 167 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 167 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 167 272
  (Polychromatic418967fa.accept_10_5_7_2_1_516 65 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 167 272 (accept_3_2 64 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 167 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 167 272 (accept_3_2 61 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 167 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 60 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 167 272
  (Polychromatic418967fa.accept_10_9_7_2_1_887 59 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 167 272 (accept_3_2 58 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 167 272 (Polychromatic418967fa.accept_13_4_11_12_1_1318 56 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 167 272 (accept_3_2 55 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 167 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 167 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 53 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 167 272 (accept_3_2 52 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 167 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 50 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 167 272 (accept_3_2 49 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 48 167 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 167 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 167 272
  (Polychromatic418967fa.accept_14_5_13_6_1_3574 47 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 167 272 (accept_3_2 46 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 167 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 167 272 (accept_3_2 43 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 167 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 167 272
  (Polychromatic418967fa.accept_25_16_17_22_1_16696 41 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 40 167 272 (accept_3_2 40 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 39 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 167 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 38 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 167 272 (accept_3_2 37 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 167 272
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 36 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 167 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 167 272 (accept_3_2 34 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 33 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 167 272
  (Polychromatic418967fa.accept_19_13_15_6_1_7131 32 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 167 272 (accept_3_2 31 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 167 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 167 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 167 272 (accept_3_2 28 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 167 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 167 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 167 272 (accept_3_2 25 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 167 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 167 272
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 167 272 (accept_3_2 22 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 167 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 167 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 167 272 (accept_3_2 19 167
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 167 272
  (Polychromatic418967fa.accept_24_18_23_8_1_8171 18 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 167 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 167 272 (accept_3_2 16 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 15 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 167 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 167 272 (accept_3_2 13 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 167 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 167 272 (Polychromatic418967fa.accept_19_11_15_6_1_7173 11 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 167 272 (accept_3_2 10 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 167 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 167 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 8 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 167 272 (accept_3_2 7 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  167 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 167 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 5 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 167 272 (accept_3_2 4 167 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 167 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 167 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 167 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 2 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 167 272 (accept_3_2 1 167 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 167
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 107 166 272 (Eq.refl Bool.true) (allA_of_3_0 107 166 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 108 165 272 (Eq.refl Bool.true) (allA_succ_of_accept 107 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 165 272 (accept_3_2 106 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 165 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 165 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 104 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 165 272 (accept_3_2 103 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 165 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 102 165
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 165 272 (accept_3_2 100 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 165 272 (Polychromatic418967fa.accept_13_8_9_12_1_2813 99 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 165 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 165 272 (accept_3_2 97 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 165 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 165 272 (accept_3_2 94 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 165 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 165 272 (Polychromatic418967fa.accept_24_20_21_8_1_9902 92 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 165 272 (accept_3_2 91 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 165 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 165
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 165 272 (accept_3_2 88 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 165 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 165 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 165 272 (accept_3_2 85 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 165 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 84 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 165 272 (accept_3_2 82 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 165 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062 81 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 165 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 165 272 (accept_3_2 79 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 165 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 165 272 (accept_3_2 76 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 165 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 165 272 (Polychromatic418967fa.accept_19_17_13_6_1_8670 74 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 165 272 (accept_3_2 73 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 165 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 165 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 165 272 (accept_3_2 70 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 165 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 165 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 165 272 (accept_3_2 67 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 165 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 165 272 (accept_3_2 64 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 165 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 165 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 165 272 (accept_3_2 61 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 165 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 165 272 (accept_3_2 58 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 165 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 57 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 165 272 (Polychromatic418967fa.accept_21_14_18_20_1_12307 56 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 165 272 (accept_3_2 55 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 165 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 165 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 165 272 (accept_3_2 52 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 165 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 165 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 165 272 (accept_3_2 49 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 165 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 165 272 (accept_3_2 46 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 165 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 165 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 165 272 (accept_3_2 43 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 165 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 165 272 (accept_3_2 40 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 165 272 (Polychromatic418967fa.accept_24_15_21_8_1_11704 39 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 38 165 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 165 272 (accept_3_2 37 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 165 272 (Polychromatic418967fa.accept_13_10_9_12_1_2814 36 165
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 165 272 (accept_3_2 34 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 165 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 165 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 165 272 (accept_3_2 31 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 165 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 165 272 (accept_3_2 28 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 165 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 165 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 165 272 (accept_3_2 25 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 165 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 165 272 (accept_3_2 22 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 165 272 (Polychromatic418967fa.accept_13_8_9_12_1_2813 21 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 165 272 (Polychromatic418967fa.accept_22_20_11_8_1_16662 20 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 165 272 (accept_3_2 19 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 165 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 165
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 165 272 (accept_3_2 16 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 165 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 165 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 165 272 (accept_3_2 13 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 165 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 165 272 (accept_3_2 10 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  165 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 165 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 165 272 (accept_3_2 7 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 165 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 165 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 165 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 165 272 (accept_3_2 4 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  165 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 165 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 165 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 165 272 (accept_3_2 1 165 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 165
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 109 164 272 (Eq.refl Bool.true) (allA_succ_of_gcd 108 164 272 4 27 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 164 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 107 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 164 272 2 53 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 164 272 (Polychromatic418967fa.accept_13_1_8_12_1_2045 105 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 164 272 4 26 41 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 164 272 (accept_3_2 103 164 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 164 272 2 51 82 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 164 272
  (Polychromatic418967fa.accept_13_10_8_12_1_2032 101 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 164 272 4 25 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 164 272 (Polychromatic418967fa.accept_19_4_12_6_1_11409 99 164 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 164 272 2 49 82 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 164 272 (accept_3_2 97
  164 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 164 272 4 24 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 164 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 164 272 2 47 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 164 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 164 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 164 272 4 23 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 164 272 (accept_3_2 91 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 164 272 2 45 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 164 272
  (Polychromatic418967fa.accept_19_13_12_6_1_11362 89 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 88 164 272 4 22 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 87 164 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 87 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 164 272 2 43 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 164 272 (accept_3_2 85 164 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 164 272 4 21 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 164 272
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 83 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 82 164 272 2 41 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 81 164 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 164 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 80 164 272 4 20 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 79 164 272 (accept_3_2 79 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78 164 272 2 39 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 77 164 272 (Polychromatic418967fa.accept_10_7_4_2_1_903
  77 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 164 272 4 19 41 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 164 272
  (Polychromatic418967fa.accept_11_9_10_8_1_444 75 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 164 272 2 37 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 164 272 (accept_3_2 73 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 164 272 4 18 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 164 272 (Polychromatic418967fa.accept_19_14_12_6_1_9964 71 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 164 272 2 35 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 164 272
  (Polychromatic418967fa.accept_13_4_8_12_1_3526 69 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 164 272 4 17 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 164 272 (accept_3_2 67 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 164 272 2 33 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 164 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 164 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 164 272 4 16 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 164 272
  (Polychromatic418967fa.accept_15_3_14_2_1_1888 63 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 164 272 2 31 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 164 272 (accept_3_2 61 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 164 272 4 15 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 164 272 (Polychromatic418967fa.accept_13_7_8_12_1_2810 59 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 164 272 2 29 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 164 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 164 272 4 14 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 164 272 (accept_3_2 55 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 164 272 2 27 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 164 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 164 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 164 272 4 13 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 164 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 164 272 2 25 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 164 272 (accept_3_2 49 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 164 272 4 12 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 164 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 47 164 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 164 272 2 23 82 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 164 272
  (Polychromatic418967fa.accept_14_3_10_6_1_1136 45 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 164 272 4 11 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 164 272 (accept_3_2 43 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 164 272 2 21 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 164 272 (Polychromatic418967fa.accept_22_19_10_8_1_9011 41 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 164 272 4 10 41 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 164 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 164 272 2 19 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 164 272 (accept_3_2 37 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 164 272 4 9 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 164 272 (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 164 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 164 272 2 17 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 164 272 (Polychromatic418967fa.accept_13_7_8_12_1_2810
  33 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 164 272 4 8 41 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 164 272
  (accept_3_2 31 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 164 272 2 15 82 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 164 272
  (Polychromatic418967fa.accept_19_10_12_6_1_7171 29 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 28 164 272 4 7 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 27 164 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 27 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 164 272 2 13 82 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 164 272 (accept_3_2 25 164 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 164 272 4 6 41 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 164 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 23 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 164 272 2 11 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 164 272 (Polychromatic418967fa.accept_19_2_12_6_1_5816 21 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 164 272 4 5 41 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 164 272 (accept_3_2 19 164 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 164 272 2 9 82 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 164 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 17 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 164 272 4 4 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 164 272 (Polychromatic418967fa.accept_19_15_12_6_1_8634 15 164 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 164 272 2 7 82 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 164 272 (accept_3_2 13 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 164 272 4 3 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 164 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11
  164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 164 272 2 5 82 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 164 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 164 272 4 2 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 164 272 (accept_3_2 7 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 164
  272 2 3 82 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  164 272 (Polychromatic418967fa.accept_13_5_8_12_1_2759 5 164 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 164 272 4 1 41 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 164 272 (Polychromatic418967fa.accept_14_3_10_6_1_1136 3 164 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 164 272 2 1 82 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 164 272 (accept_3_2 1 164 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 164
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 110 163 272 (Eq.refl Bool.true) (allA_of_3_0 110 163 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 111 162 272 (Eq.refl Bool.true) (allA_succ_of_gcd 110 162 272 2 55 81 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 162 272 (accept_3_2 109 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 162 272 2 54 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 162 272 (Polychromatic418967fa.accept_7_2_1_6_1_173
  107 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 162 272 2 53 81 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 162 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 105 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 162 272 2 52 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 162 272 (accept_3_2 103 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 162 272 2 51 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 162 272 (Polychromatic418967fa.accept_13_10_6_12_1_2780 101 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 162 272 2 50 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 162 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 99 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 162 272 2 49 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 162 272 (accept_3_2 97 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 162 272 2 48 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 162 272 (Polychromatic418967fa.accept_15_5_12_2_1_2820 95 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 162 272 2 47 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 162 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 162 272 2 46 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 162 272 (accept_3_2 91 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 162 272 2 45 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 162 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 162 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 162 272 2 44 81 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 162 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 162 272 2 43 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 162 272 (accept_3_2 85 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 162 272 2 42 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 162 272 (Polychromatic418967fa.accept_13_5_6_12_1_2750 83 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 162 272 2 41 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 162 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 81 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 162 272 2 40 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 162 272 (accept_3_2 79 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 162 272 2 39 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 162 272 (Polychromatic418967fa.accept_14_7_8_6_1_1164 77 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 162 272 2 38 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 162 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 162 272 2 37 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 162 272 (accept_3_2 73 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 162 272 2 36 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 162 272 (Polychromatic418967fa.accept_19_14_10_6_1_4372 71 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 162 272 2 35 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 162 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 162 272 2 34 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 162 272 (accept_3_2 67 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 162 272 2 33 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 162 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 162 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 162 272 2 32 81 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 162 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 162 272 2 31 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 162 272 (accept_3_2 61 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 162 272 2 30 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 162 272 (Polychromatic418967fa.accept_13_7_6_12_1_2027 59 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 162 272 2 29 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 162 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 57 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 162 272 2 28 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 162 272 (accept_3_2 55 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 162 272 2 27 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 162 272 (Polychromatic418967fa.accept_19_15_10_6_1_7169 53 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 162 272 2 26 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 162 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 162 272 2 25 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 162 272 (accept_3_2 49 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 162 272 2 24 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 162 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 162 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 162 272 2 23 81 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 162 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 162 272 2 22 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 162 272 (accept_3_2 43 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 162 272 2 21 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 162 272 (Polychromatic418967fa.accept_13_2_6_12_1_1334 41 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 162 272 2 20 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 162 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 162 272 2 19 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 162 272 (accept_3_2 37 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 162 272 2 18 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 162 272 (Polychromatic418967fa.accept_14_7_8_6_1_1164 35 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 162 272 2 17 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 162 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 162 272 2 16 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 162 272 (accept_3_2 31 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 162 272 2 15 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 162 272 (Polychromatic418967fa.accept_15_14_12_2_1_3804 29 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 162 272 2 14 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 162 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 162 272 2 13 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 162 272 (accept_3_2 25 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 162 272 2 12 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 162 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 162 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 162 272 2 11 81 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 162 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 162 272 2 10 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 162 272 (accept_3_2 19 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 162 272 2 9 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 162 272 (Polychromatic418967fa.accept_20_17_2_12_1_8168 17 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 162 272 2 8 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 162 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 162 272 2 7 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 162 272 (accept_3_2 13 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 162 272 2 6 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 162 272 (Polychromatic418967fa.accept_24_11_18_8_1_16695 11 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 162 272 2 5 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 162 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 162 272 2 4 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 162 272 (accept_3_2 7 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 162
  272 2 3 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  162 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 162 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 162 272 2 2 81 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 162 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 3 162 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 162 272 2 1 81 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 162 272 (accept_3_2 1 162 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 162
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 112 161 272 (Eq.refl Bool.true) (allA_succ_of_accept 111 161 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 111 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 110 161 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 110 161 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 161 272 (accept_3_2 109 161 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 108 161 272 (Polychromatic418967fa.accept_13_4_5_12_1_751 108 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 161 272
  (Polychromatic418967fa.accept_21_2_14_20_1_841 107 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 106 161 272 (accept_3_2 106 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 105 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 161 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 161 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 104 161
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 161 272 (accept_3_2 103 161
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 161 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 102 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 101 161 272 (Polychromatic418967fa.accept_18_11_17_2_1_6349 101 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 161 272 (accept_3_2 100 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 99 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 161 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 98 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 161 272 (accept_3_2 97 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 161 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 161 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 161 272 (accept_3_2 94 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 161 272
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 92 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 161 272 (accept_3_2 91 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 161 272 (Polychromatic418967fa.accept_19_14_9_6_1_8633 90 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 161 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 89 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 161 272 (accept_3_2 88 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 161 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 161 272 (accept_3_2 85 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 161 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 161 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 83 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 161 272 (accept_3_2 82 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 81 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 161 272
  (Polychromatic418967fa.accept_13_2_5_12_1_2043 80 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 161 272 (accept_3_2 79 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 161 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 161 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 161 272 (accept_3_2 76 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 161 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 161 272 (accept_3_2 73 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 161 272 (Polychromatic418967fa.accept_13_7_5_12_1_1305 72 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 161 272 (Polychromatic418967fa.accept_13_6_5_12_1_307 71 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 161 272 (accept_3_2 70 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 161 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 161 272 (accept_3_2 67 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 161 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 161 272 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 161 272 (accept_3_2 64 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 161 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 62 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 161 272 (accept_3_2 61 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 161 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 161 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 161 272 (accept_3_2 58 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 161 272
  (Polychromatic418967fa.accept_10_6_1_2_1_874 56 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 161 272 (accept_3_2 55 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 161 272 (Polychromatic418967fa.accept_13_2_5_12_1_2043 54 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 161 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 53 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 161 272 (accept_3_2 52 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 161 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 161 272 (accept_3_2 49 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 161 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 161 272 (Polychromatic418967fa.accept_13_8_5_12_1_2755 47 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 161 272 (accept_3_2 46 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 161 272
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 44 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 161 272 (accept_3_2 43 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 161 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 161 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 161 272 (accept_3_2 40 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 161 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 38 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 161 272 (accept_3_2 37 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 161 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 161 272 (Polychromatic418967fa.accept_15_5_11_2_1_1095 35 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 161 272 (accept_3_2 34 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 161 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 161 272 (accept_3_2 31 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 161 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 161 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 29 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 161 272 (accept_3_2 28 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 161 272
  (Polychromatic418967fa.accept_10_6_1_2_1_874 26 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 161 272 (accept_3_2 25 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 161 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 161 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 161 272 (accept_3_2 22 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 161 272
  (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 161 272 (accept_3_2 19 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 161 272 (Polychromatic418967fa.accept_19_18_9_6_1_5815 18 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 161 272 (Polychromatic418967fa.accept_13_4_5_12_1_751 17 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 161 272 (accept_3_2 16 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 161 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 161 272 (accept_3_2 13 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 161 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 161 272 (Polychromatic418967fa.accept_18_11_17_2_1_6349 11 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 161 272 (accept_3_2 10 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 161 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 161 272
  (Polychromatic418967fa.accept_13_8_5_12_1_2755 8 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 161 272 (accept_3_2 7 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  161 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 161 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 161 272 (accept_3_2 4 161 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 161 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 161 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 161 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 161 272 (accept_3_2 1 161 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 161
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 113 160 272 (Eq.refl Bool.true) (allA_of_3_0 113 160 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 114 159 272 (Eq.refl Bool.true) (allA_succ_of_accept 113 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 159 272 (accept_3_2 112 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 111 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 159 272 (Polychromatic418967fa.accept_25_10_9_22_1_11469 110 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 159 272 (accept_3_2 109 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 159 272 (Polychromatic418967fa.accept_13_4_3_12_1_2066 108
  159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 159 272 (accept_3_2 106 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 159 272 (Polychromatic418967fa.accept_22_17_5_8_1_16694 105 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 159 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 104 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 159 272 (accept_3_2 103 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 159 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 159
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 159 272 (accept_3_2 100 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 159 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 159 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 159 272 (accept_3_2 97 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 159 272 (Polychromatic418967fa.accept_19_1_7_6_1_1959 96 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 159 272 (accept_3_2 94 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 159 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 92 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 159 272 (accept_3_2 91 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 159 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 159 272 (accept_3_2 88 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 159 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 87 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 159 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 86 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 159 272 (accept_3_2 85 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 159 272 (accept_3_2 82 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 159 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 81 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 159 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 159 272 (accept_3_2 79 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 159 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 159 272 (accept_3_2 76 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 75 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 159 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 159 272 (accept_3_2 73 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 159 272 (Polychromatic418967fa.accept_21_9_12_20_1_10792 72 159 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 159 272 (accept_3_2 70 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 159 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 69 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 159 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 68 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 159 272 (accept_3_2 67 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 159 272 (accept_3_2 64 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 159 272 (Polychromatic418967fa.accept_22_19_5_8_1_16693 63 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 159 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 159 272 (accept_3_2 61 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 159 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 159 272 (accept_3_2 58 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 159 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 57 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 159 272 (Polychromatic418967fa.accept_13_4_3_12_1_2066 56 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 159 272 (accept_3_2 55 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 159 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 159
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 159 272 (accept_3_2 52 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 159 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 51 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 159 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 159 272 (accept_3_2 49 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 159 272 (accept_3_2 46 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 159 272 (Polychromatic418967fa.accept_21_3_12_20_1_1891 45 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 159 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 44 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 159 272 (accept_3_2 43 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 159 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 159 272 (accept_3_2 40 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 159 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 159 272 (Polychromatic418967fa.accept_15_8_9_2_1_1897 38 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 159 272 (accept_3_2 37 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 159 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 159 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 159 272 (accept_3_2 34 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 159 272 (Polychromatic418967fa.accept_19_14_7_6_1_8654 33 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 159 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 159 272 (accept_3_2 31 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 30 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 159 272 (accept_3_2 28 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 159 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 159 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 26 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 159 272 (accept_3_2 25 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 159 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 24 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 159 272 (accept_3_2 22 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 159 272 (Polychromatic418967fa.accept_19_1_7_6_1_1959 20 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 159 272 (accept_3_2 19 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 159 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 159 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 159 272 (accept_3_2 16 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 159 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 159 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 159 272 (accept_3_2 13 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 12 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 159 272 (accept_3_2 10 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  159 272 (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 159 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 159 272 (accept_3_2 7 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 159 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 159 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 159 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 159 272 (accept_3_2 4 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  159 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 159 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 159 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 2 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 159 272 (accept_3_2 1 159 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 159
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 115 158 272 (Eq.refl Bool.true) (allA_succ_of_gcd 114 158 272 2 57 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 158 272
  (Polychromatic418967fa.accept_12_5_2_8_1_172 113 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 158 272 2 56 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 158 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 111 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 158 272 2 55 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 158 272 (accept_3_2 109 158 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 158 272 2 54 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 158 272 (Polychromatic418967fa.accept_7_2_4_6_1_166
  107 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 158 272 2 53 79 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 158 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 105 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 158 272 2 52 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 158 272 (accept_3_2 103 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 158 272 2 51 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 158 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 101 158 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 158 272 2 50 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 158 272
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 99 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 158 272 2 49 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 158 272 (accept_3_2 97 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 158 272 2 48 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 158 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 95 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 158 272 2 47 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 158 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 158 272 2 46 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 158 272 (accept_3_2 91 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 158 272 2 45 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 158 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 158 272 2 44 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 158 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 158 272 2 43 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 158 272 (accept_3_2 85 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 158 272 2 42 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 158 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 158 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 158 272 2 41 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 158 272
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 81 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 158 272 2 40 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 158 272 (accept_3_2 79 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 158 272 2 39 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 158 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 158 272 2 38 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 158 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 75 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 158 272 2 37 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 158 272 (accept_3_2 73 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 158 272 2 36 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 158 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 158 272 2 35 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 158 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 158 272 2 34 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 158 272 (accept_3_2 67 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 158 272 2 33 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 158 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 158 272 2 32 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 158 272
  (Polychromatic418967fa.accept_23_17_20_19_1_8574 63 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 158 272 2 31 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 158 272 (accept_3_2 61 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 158 272 2 30 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 158 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 158 272 2 29 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 158 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 158 272 2 28 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 158 272 (accept_3_2 55 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 158 272 2 27 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 158 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 158 272 2 26 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 158 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 51 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 158 272 2 25 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 158 272 (accept_3_2 49 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 158 272 2 24 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 158 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 158 272 2 23 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 158 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 45 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 158 272 2 22 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 158 272 (accept_3_2 43 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 158 272 2 21 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 158 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 41 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 158 272 2 20 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 158 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 158 272 2 19 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 158 272 (accept_3_2 37 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 158 272 2 18 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 158 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 158 272 2 17 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 158 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 158 272 2 16 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 158 272 (accept_3_2 31 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 158 272 2 15 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 158 272 (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 158 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 158 272 2 14 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 158 272
  (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 158 272 2 13 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 158 272 (accept_3_2 25 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 158 272 2 12 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 158 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 158 272 2 11 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 158 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 158 272 2 10 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 158 272 (accept_3_2 19 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 158 272 2 9 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 158 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 158 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 158 272 2 8 79 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 158 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 15 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 158 272 2 7 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 158 272 (accept_3_2 13 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 158 272 2 6 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 158 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 158 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 158 272 2 5 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 158 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 158 272 2 4 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 158 272 (accept_3_2 7 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 158
  272 2 3 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  158 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 158 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 158 272 2 2 79 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 158 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 158 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 158 272 2 1 79 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 158 272 (accept_3_2 1 158 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 158
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 116 157 272 (Eq.refl Bool.true) (allA_of_3_0 116 157 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 117 156 272 (Eq.refl Bool.true) (allA_succ_of_gcd 116 156 272 4 29 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 156 272 (accept_3_2 115 156 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 156 272 2 57 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 156 272 (Polychromatic418967fa.accept_7_1_2_6_1_55
  113 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 156 272 4 28 39 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 156 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 111 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 156 272 2 55 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 156 272 (accept_3_2 109 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 156 272 4 27 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 156 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 107 156 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 156 272 2 53 78 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 156 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 105 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 156 272 4 26 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 156 272 (accept_3_2 103 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 156 272 2 51 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 156 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 101 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 156 272 4 25 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 156 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 99 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 156 272 2 49 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 156 272 (accept_3_2 97 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 156 272 4 24 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 156 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 156 272 2 47 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 156 272
  (Polychromatic418967fa.accept_11_5_2_8_1_866 93 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 156 272 4 23 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 156 272 (accept_3_2 91 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 156 272 2 45 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 156 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 156 272 4 22 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 156 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 87 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 156 272 2 43 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 156 272 (accept_3_2 85 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 156 272 4 21 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 156 272 (Polychromatic418967fa.accept_15_8_6_2_1_1128 83 156 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 156 272 2 41 78 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 156 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 156 272 4 20 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 156 272 (accept_3_2 79 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 156 272 2 39 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 156 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 156 272 4 19 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 156 272
  (Polychromatic418967fa.accept_18_3_12_2_1_2639 75 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 156 272 2 37 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 156 272 (accept_3_2 73 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 156 272 4 18 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 156 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 71 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 156 272 2 35 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 156 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 156 272 4 17 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 156 272 (accept_3_2 67 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 156 272 2 33 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 156 272 (Polychromatic418967fa.accept_21_2_9_20_1_9260 65 156 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 156 272 4 16 39 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 156 272
  (Polychromatic418967fa.accept_23_17_18_19_1_10210 63 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 156 272 2 31 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 156 272 (accept_3_2 61 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 156 272 4 15 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 156 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 156 272 2 29 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 156 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 156 272 4 14 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 156 272 (accept_3_2 55 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 156 272 2 27 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 156 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 156 272 4 13 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 156 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 156 272 2 25 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 156 272 (accept_3_2 49 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 156 272 4 12 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 156 272 (Polychromatic418967fa.accept_23_1_18_19_1_16692 47 156 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 156 272 2 23 78 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 156 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 45 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 156 272 4 11 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 156 272 (accept_3_2 43 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 156 272 2 21 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 156 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 156 272 4 10 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 156 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 39 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 156 272 2 19 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 156 272 (accept_3_2 37 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 156 272 4 9 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 156 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 156 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 156 272 2 17 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 156 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33
  156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 156 272 4 8 39 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 156 272 (accept_3_2 31
  156 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 156 272 2 15 78 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 156 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 156 272 4 7 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 156 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 156 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 156 272 2 13 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 156 272 (accept_3_2 25 156 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 156 272 4 6 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 156 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 156 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 156 272 2 11 78 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 156 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 156 272 4 5 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 156 272 (accept_3_2 19 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  156 272 2 9 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 156 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 156 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 156 272 4 4 39 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 156 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15
  156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 156 272 2 7 78 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 156 272 (accept_3_2 13
  156 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 156 272 4 3 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 156 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 11 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 10 156 272 2 5 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 9 156 272 (Polychromatic418967fa.accept_25_9_6_22_1_16691 9 156 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 156 272 4 2 39 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 156 272 (accept_3_2 7 156 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 156 272 2 3 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 156 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5
  156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 156 272 4 1 39 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 156 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 3 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 156 272 2 1 78 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 156 272 (accept_3_2 1 156 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 156
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 118 155 272 (Eq.refl Bool.true) (allA_succ_of_accept 117 155 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 117 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 116 155 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 116 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 155 272 (accept_3_2 115 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 114 155 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 114 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 155 272
  (Polychromatic418967fa.accept_10_3_5_2_1_38 113 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 155 272 (accept_3_2 112 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 155 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 110 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 155 272 (accept_3_2 109 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 155 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 108 155
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 155 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 107 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 155 272 (accept_3_2 106 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 155 272 (Polychromatic418967fa.accept_15_14_5_2_1_4761 104 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 155 272 (accept_3_2 103 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 155 272 (Polychromatic418967fa.accept_15_12_5_2_1_2786 102
  155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 155 272
  (Polychromatic418967fa.accept_15_11_5_2_1_520 101 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 155 272 (accept_3_2 100 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 155 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 98 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 155 272 (accept_3_2 97 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 155 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 155 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 155 272
  (Polychromatic418967fa.accept_21_11_8_20_1_4591 95 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 94 155 272 (accept_3_2 94 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 93 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 155 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 155 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 92 155
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 155 272 (accept_3_2 91 155
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 155 272
  (Polychromatic418967fa.accept_20_10_15_12_1_11131 90 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 155 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 155 272 (accept_3_2 88 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 87 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 155 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 86 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 155 272 (accept_3_2 85 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 155 272 (Polychromatic418967fa.accept_19_8_3_6_1_9982 84 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 155 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 83 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 155 272 (accept_3_2 82 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 155 272
  (Polychromatic418967fa.accept_19_4_3_6_1_11389 80 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 155 272 (accept_3_2 79 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 155 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 78 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 155 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 77 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 155 272 (accept_3_2 76 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 75 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 155 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 155 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 74 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 155 272 (accept_3_2 73 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 155 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 155 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 71 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 155 272 (accept_3_2 70 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 155 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 155 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 68 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 155 272 (accept_3_2 67 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 155 272 (Polychromatic418967fa.accept_19_9_3_6_1_11390 66 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 155 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 155 272 (accept_3_2 64 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 63 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 155 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 62 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 155 272 (accept_3_2 61 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 155 272 (Polychromatic418967fa.accept_24_12_11_8_1_16690 60 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 59 155 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 59 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 155 272 (accept_3_2 58 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 155 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 155 272
  (Polychromatic418967fa.accept_15_11_5_2_1_520 56 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 155 272 (accept_3_2 55 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 155 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 155 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 53 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 155 272 (accept_3_2 52 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 155 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 50 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 155 272 (accept_3_2 49 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 155 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 155 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 155 272 (accept_3_2 46 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 155 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 44 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 155 272 (accept_3_2 43 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 155 272 (Polychromatic418967fa.accept_15_12_5_2_1_2786 42 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 155 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 41 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 155 272 (accept_3_2 40 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 155 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 155 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 155 272 (accept_3_2 37 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 155 272 (Polychromatic418967fa.accept_19_17_3_6_1_8662 36 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 155 272 (Polychromatic418967fa.accept_14_7_1_6_1_3514 35 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 155 272 (accept_3_2 34 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 155 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 155 272
  (Polychromatic418967fa.accept_18_14_11_2_1_5068 32 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 155 272 (accept_3_2 31 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 155 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 155 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 155 272 (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 155
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 155 272 (accept_3_2 28 155
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 155 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 27 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 155 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 155 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 155 272 (accept_3_2 25 155 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 24 155 272 (Polychromatic418967fa.accept_19_5_3_6_1_8642 24 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 155 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 23 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 155 272 (accept_3_2 22 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 155 272 (Polychromatic418967fa.accept_19_1_3_6_1_5827 20 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 155 272 (accept_3_2 19 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 155 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 155
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 155 272
  (Polychromatic418967fa.accept_10_7_5_2_1_880 17 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 155 272 (accept_3_2 16 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 155 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 155 272 (accept_3_2 13 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 155 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 155 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 155 272
  (Polychromatic418967fa.accept_15_11_5_2_1_520 11 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 155 272 (accept_3_2 10 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 155 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 8 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 155 272 (accept_3_2 7 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 155 272 (Polychromatic418967fa.accept_20_6_15_12_1_6637 6 155 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 155 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 5 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 155 272 (accept_3_2 4 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  155 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 155 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 155 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 155 272 (accept_3_2 1 155 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 155
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 119 154 272 (Eq.refl Bool.true) (allA_of_3_0 119 154 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 120 153 272 (Eq.refl Bool.true) (allA_succ_of_gcd 119 153 272 17 7 9 16 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 118 153 272 (accept_3_2 118 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 153 272 (Polychromatic418967fa.accept_14_5_13_6_1_3574 117
  153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 153 272
  (Polychromatic418967fa.accept_19_2_1_6_1_5780 116 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 153 272 (accept_3_2 115 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 153 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 114 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 113 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 153 272 (accept_3_2 112 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 153 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 111 153
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 153 272
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 110 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 109 153 272 (accept_3_2 109 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 108 153 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 108 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68
  107 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 153 272 (accept_3_2
  106 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 153 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 105 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 104 153 272 (Polychromatic418967fa.accept_15_14_3_2_1_2811 104 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 153 272 (accept_3_2 103 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 102 153 272 17 6 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 101 153 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 153 272 (accept_3_2 100 153 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 153 272
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 99 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 153 272 (Polychromatic418967fa.accept_13_7_10_12_1_2047 98 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 153 272 (accept_3_2 97 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 153 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 96 153
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 153 272 (accept_3_2 94 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 153 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 93 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 153 272 (Polychromatic418967fa.accept_22_4_21_8_1_8923 92 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 153 272 (accept_3_2 91 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 153 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 153
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 153 272 (accept_3_2 88 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 153 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 87 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 153 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 86 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 85 153 272 17 5 9 16 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 84 153 272
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 84 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 83 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 153 272 (accept_3_2 82 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 153 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 153 272
  (Polychromatic418967fa.accept_13_2_10_12_1_757 80 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 153 272 (accept_3_2 79 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 153 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 77 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 153 272 (accept_3_2 76 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 153 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 75 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 153 272
  (Polychromatic418967fa.accept_13_9_10_12_1_2048 74 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 73 153 272 (accept_3_2 73 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 72 153 272 (Polychromatic418967fa.accept_13_7_10_12_1_2047 72 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 71
  153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 153 272 (accept_3_2 70
  153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 153 272
  (Polychromatic418967fa.accept_25_19_3_22_1_14954 69 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 68 153 272 17 4 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 67 153 272 (accept_3_2 67 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 153 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 153 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 65 153 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 153 272 (accept_3_2 64 153 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 153 272
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 153 272 (Polychromatic418967fa.accept_19_5_1_6_1_4361 62 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 153 272 (accept_3_2 61 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 153 272 (Polychromatic418967fa.accept_13_8_10_12_1_1337 60 153
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 153 272 (accept_3_2 58 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 153 272 (Polychromatic418967fa.accept_15_12_3_2_1_2756 57 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 153 272 (Polychromatic418967fa.accept_19_18_1_6_1_5807 56 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 153 272 (accept_3_2 55 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 153 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 153
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 153 272 (accept_3_2 52 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 51
  153 272 17 3 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept
  50 153 272 (Polychromatic418967fa.accept_13_11_10_12_1_1338 50 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 49 153 272 (accept_3_2 49 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 48 153 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 48 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 47
  153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 153 272 (accept_3_2 46
  153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 153 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 45 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 44 153 272 (Polychromatic418967fa.accept_15_14_3_2_1_2811 44 153 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 153 272 (accept_3_2 43 153 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 42 153 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 42 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 153 272 (accept_3_2 40 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 153 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 39 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 153 272 (Polychromatic418967fa.accept_24_14_9_8_1_11688 38 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 153 272 (accept_3_2 37 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 153 272 (Polychromatic418967fa.accept_21_15_6_20_1_12272 36
  153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 153 272 17 2 9 16 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 33 153 272 (Polychromatic418967fa.accept_13_7_10_12_1_2047 33 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 153 272
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 32 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 31 153 272 (accept_3_2 31 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 30 153 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 30 153 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 153 272 (Polychromatic418967fa.accept_6_5_3_2_1_68 29 153 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 153 272 (accept_3_2 28 153 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 153 272
  (Polychromatic418967fa.accept_15_12_3_2_1_2756 27 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 26 153 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 26 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 153 272 (accept_3_2 25 153 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 153 272 (Polychromatic418967fa.accept_13_11_10_12_1_1338 24 153 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 153 272 (accept_3_2 22 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 153 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 21 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 153 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 153 272 (accept_3_2 19 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 153 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 153
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 17 153 272 17 1 9 16 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 16 153 272 (accept_3_2 16
  153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 153 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 15 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 14 153 272 (Polychromatic418967fa.accept_15_14_3_2_1_2811 14 153 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 153 272 (accept_3_2 13 153 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 12 153 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 12 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 153 272 (accept_3_2 10 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  153 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 9 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 153 272 (Polychromatic418967fa.accept_13_8_10_12_1_1337 8 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 153 272 (accept_3_2 7 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 153 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 6 153 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 153 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 153 272 (accept_3_2 4 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  153 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 3 153 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 153 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 2 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 153 272 (accept_3_2 1 153 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 153
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 121 152 272 (Eq.refl Bool.true) (allA_succ_of_gcd 120 152 272 8 15 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 152 272
  (Polychromatic418967fa.accept_21_14_5_20_1_12299 119 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 152 272 2 59 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 117 152 272 (Polychromatic418967fa.accept_25_17_2_22_1_7827 117 152 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 152 272 4 29 38 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 152 272 (accept_3_2
  115 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 152 272 2 57 76 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 152 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 113 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 152 272 8 14 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 152 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 111 152 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 152 272 2 55 76 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 152 272 (accept_3_2 109 152 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 152 272 4 27 38 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 152 272
  (Polychromatic418967fa.accept_13_3_9_12_1_2062 107 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 106 152 272 2 53 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 105 152 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 105 152 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 152 272 8 13 19 34 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 152 272 (accept_3_2 103 152 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 152 272 2 51 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 152 272
  (Polychromatic418967fa.accept_13_10_9_12_1_2814 101 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 152 272 4 25 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 152 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 99 152 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 152 272 2 49 76 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 152 272 (accept_3_2 97 152 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 152 272 8 12 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 152 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 95 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 152 272 2 47 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 152 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 93 152 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 152 272 4 23 38 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 152 272 (accept_3_2 91 152 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 152 272 2 45 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 152 272 (Polychromatic418967fa.accept_18_17_8_2_1_2622
  89 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 152 272 8 11 19 34
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 152 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 87 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 152 272 2 43 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 152 272 (accept_3_2 85 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 152 272 4 21 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 152 272 (Polychromatic418967fa.accept_14_13_12_6_1_2735 83 152 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 152 272 2 41 76 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 152 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 152 272 8 10 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 152 272 (accept_3_2 79 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 152 272 2 39 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 152 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 152 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 152 272 4 19 38 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 152 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 75 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 152 272 2 37 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 152 272 (accept_3_2 73 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 152 272 8 9 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 71 152 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 152 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 152 272 2 35 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 152 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 69
  152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 152 272 4 17 38 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 152 272 (accept_3_2 67
  152 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 152 272 2 33 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 152 272
  (Polychromatic418967fa.accept_11_10_9_8_1_1974 65 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 152 272 8 8 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 152 272 (Polychromatic418967fa.accept_22_19_20_8_1_8920 63 152 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 152 272 2 31 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 152 272 (accept_3_2 61 152 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 152 272 4 15 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 152 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59
  152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 152 272 2 29 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 152 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 152 272 8 7 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 152 272 (accept_3_2 55 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  152 272 2 27 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 152 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 152 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 152 272 4 13 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 152 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 51
  152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 152 272 2 25 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 152 272 (accept_3_2 49
  152 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 152 272 8 6 19 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 152 272
  (Polychromatic418967fa.accept_13_8_9_12_1_2813 47 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 152 272 2 23 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 152 272 (Polychromatic418967fa.accept_22_1_20_8_1_4017 45 152 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 152 272 4 11 38 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 152 272 (accept_3_2 43 152 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 152 272 2 21 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 152 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 41 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 40 152 272 8 5 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 39 152 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 39 152 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 152 272 2 19 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 152 272 (accept_3_2 37 152 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 36 152 272 4 9 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 152 272 (Polychromatic418967fa.accept_18_17_8_2_1_2622 35 152
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 152 272 2 17 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 152 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 33 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 152 272 8 4 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 152 272 (accept_3_2 31 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  152 272 2 15 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 152 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 152 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 152 272 4 7 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 152 272
  (Polychromatic418967fa.accept_14_13_12_6_1_2735 27 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 26 152 272 2 13 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 25 152 272 (accept_3_2 25 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 152 272 8 3 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 23 152 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 152 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 152 272 2 11 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 152 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 21
  152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 152 272 4 5 38 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 152 272 (accept_3_2 19
  152 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 152 272 2 9 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 152 272
  (Polychromatic418967fa.accept_18_17_8_2_1_2622 17 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 152 272 8 2 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 152 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 15 152 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 152 272 2 7 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 152 272 (accept_3_2 13 152 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 152 272 4 3 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 152 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 152 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 152 272 2 5 76 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 152 272
  (Polychromatic418967fa.accept_25_9_2_22_1_14921 9 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 152 272 8 1 19 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 152 272 (accept_3_2 7 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 152
  272 2 3 76 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  152 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 152 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 152 272 4 1 38 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 152 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 152 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 152 272 2 1 76 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 152 272 (accept_3_2 1 152 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 152
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 122 151 272 (Eq.refl Bool.true) (allA_of_3_0 122 151 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 123 150 272 (Eq.refl Bool.true) (allA_succ_of_gcd 122 150 272 2 61 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 150 272 (accept_3_2 121 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 150 272 2 60 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 150 272
  (Polychromatic418967fa.accept_22_9_18_8_1_8979 119 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 150 272 2 59 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 117 150 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 117 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 150 272 2 58 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 150 272 (accept_3_2 115 150 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 150 272 2 57 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 150 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 113 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 150 272 2 56 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 150 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 111 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 150 272 2 55 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 150 272 (accept_3_2 109 150 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 150 272 2 54 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 150 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 107 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 150 272 2 53 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 150 272 (Polychromatic418967fa.accept_12_9_6_8_1_518 105 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 150 272 2 52 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 150 272 (accept_3_2 103 150 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 150 272 2 51 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 150 272
  (Polychromatic418967fa.accept_13_10_7_12_1_2782 101 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 150 272 2 50 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 150 272 (Polychromatic418967fa.accept_12_3_6_8_1_969 99 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 150 272 2 49 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 150 272 (accept_3_2 97 150 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 150 272 2 48 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 150 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 95 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 150 272 2 47 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 150 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 150 272 2 46 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 150 272 (accept_3_2 91 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 150 272 2 45 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 150 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 89
  150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 150 272 2 44 75 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 150 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 150 272 2 43 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 150 272 (accept_3_2 85 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 150 272 2 42 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 150 272 (Polychromatic418967fa.accept_13_5_7_12_1_2757 83 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 150 272 2 41 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 150 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 81 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 150 272 2 40 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 150 272 (accept_3_2 79 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 150 272 2 39 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 150 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 150 272 2 38 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 150 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 150 272 2 37 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 150 272 (accept_3_2 73 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 150 272 2 36 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 150 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 150 272 2 35 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 150 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 69 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 150 272 2 34 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 150 272 (accept_3_2 67 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 150 272 2 33 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 150 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 150 272 2 32 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 150 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 150 272 2 31 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 150 272 (accept_3_2 61 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 150 272 2 30 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 150 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 150 272 2 29 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 150 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 150 272 2 28 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 150 272 (accept_3_2 55 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 150 272 2 27 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 150 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 150 272 2 26 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 150 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 51 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 150 272 2 25 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 150 272 (accept_3_2 49 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 150 272 2 24 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 150 272 (Polychromatic418967fa.accept_13_8_7_12_1_3637 47 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 150 272 2 23 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 150 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 150 272 2 22 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 150 272 (accept_3_2 43 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 150 272 2 21 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 150 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 150 272 2 20 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 150 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 39 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 150 272 2 19 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 150 272 (accept_3_2 37 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 150 272 2 18 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 150 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 150 272 2 17 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 150 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 150 272 2 16 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 150 272 (accept_3_2 31 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 150 272 2 15 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 150 272 (Polychromatic418967fa.accept_22_7_18_8_1_13589 29 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 150 272 2 14 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 150 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 150 272 2 13 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 150 272 (accept_3_2 25 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 150 272 2 12 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 150 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 150 272 2 11 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 150 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 150 272 2 10 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 150 272 (accept_3_2 19 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 150 272 2 9 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 150 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 150 272 2 8 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 150 272
  (Polychromatic418967fa.accept_11_4_7_8_1_1926 15 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 150 272 2 7 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 150 272 (accept_3_2 13 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 150 272 2 6 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 150 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 150 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 150 272 2 5 75 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 150 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 9 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 150 272 2 4 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 150 272 (accept_3_2 7 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 150
  272 2 3 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  150 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 150 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 150 272 2 2 75 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 150 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 150 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 150 272 2 1 75 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 150 272 (accept_3_2 1 150 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 150
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 124 149 272 (Eq.refl Bool.true) (allA_succ_of_accept 123 149 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 123 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 122 149 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 122 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 149 272 (accept_3_2 121 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 149 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 120 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 149 272
  (Polychromatic418967fa.accept_13_2_6_12_1_1334 119 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 149 272 (accept_3_2 118 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 149 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 116 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 149 272 (accept_3_2 115 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 149 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 114 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 149 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 113 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 149 272 (accept_3_2 112 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 149 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 110 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 149 272 (accept_3_2 109 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 149 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 108 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 149 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 107 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 149 272 (accept_3_2 106 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 149 272
  (Polychromatic418967fa.accept_19_9_16_6_1_5774 104 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 149 272 (accept_3_2 103 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 149 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 102 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 149 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 101 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 149 272 (accept_3_2 100 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 149 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 149 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 149 272 (accept_3_2 97 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 149 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 149 272 (Polychromatic418967fa.accept_7_4_2_6_1_337
  95 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 149 272 (accept_3_2 94
  149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 149 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 93 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 149 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 92 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 149 272 (accept_3_2 91 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 149 272 (Polychromatic418967fa.accept_21_6_2_20_1_7803 90 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 149 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 149 272 (accept_3_2 88 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 149 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 86 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 149 272 (accept_3_2 85 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 149 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 149 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 149 272
  (Polychromatic418967fa.accept_13_5_6_12_1_2750 83 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 149 272 (accept_3_2 82 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 149 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 80 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 149 272 (accept_3_2 79 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 149 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 149 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 77 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 149 272 (accept_3_2 76 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 149 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 74 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 149 272 (accept_3_2 73 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 149 272 (Polychromatic418967fa.accept_13_7_6_12_1_2027 72 149 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 149 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 149 272 (accept_3_2 70 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 149 272 (Polychromatic418967fa.accept_19_11_16_6_1_7155 68 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 149 272 (accept_3_2 67 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 149 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 149 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 149 272
  (Polychromatic418967fa.accept_15_5_14_2_1_1876 65 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 149 272 (accept_3_2 64 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 149 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 149 272 (accept_3_2 61 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 149 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 149 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 59 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 149 272 (accept_3_2 58 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 149 272 (Polychromatic418967fa.accept_21_14_2_20_1_12297 56 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 149 272 (accept_3_2 55 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 149 272 (Polychromatic418967fa.accept_13_2_6_12_1_1334 54 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 149 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 53 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 149 272 (accept_3_2 52 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 149 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 149 272 (accept_3_2 49 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 149 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 149 272
  (Polychromatic418967fa.accept_10_7_9_2_1_1887 47 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 149 272 (accept_3_2 46 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 149 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 149 272 (accept_3_2 43 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 149 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 149 272
  (Polychromatic418967fa.accept_10_1_9_2_1_45 41 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 149 272 (accept_3_2 40 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 149 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 149 272 (accept_3_2 37 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 149 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 149 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 149 272 (accept_3_2 34 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 149 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 149 272 (accept_3_2 31 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 149 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 149 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 149 272 (accept_3_2 28 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 149 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 149 272 (accept_3_2 25 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 149 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 149 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 149 272
  (Polychromatic418967fa.accept_13_10_6_12_1_2780 23 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 22 149 272 (accept_3_2 22 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 21 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 149 272 (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 149 272 (accept_3_2 19 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 149 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 18 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 17 149 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 17 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 149 272 (accept_3_2 16 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 15 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 149 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924
  14 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 149 272 (accept_3_2 13
  149 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 149 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 12 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 11 149 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 149 272 (accept_3_2 10 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 9 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 149 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 8
  149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 149 272 (accept_3_2 7 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6 149 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 6 149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 5 149 272 (Polychromatic418967fa.accept_13_5_6_12_1_2750 5 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 149 272 (accept_3_2 4 149 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 3 149 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 149 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 149 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 2
  149 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 149 272 (accept_3_2 1 149
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 149
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 125 148 272 (Eq.refl Bool.true) (allA_of_3_0 125 148 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 126 147 272 (Eq.refl Bool.true) (allA_succ_of_accept 125 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 147 272 (accept_3_2 124 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 123 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 147 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 122 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 147 272 (accept_3_2 121 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 147 272 (Polychromatic418967fa.accept_13_3_4_12_1_36 120 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 147 272 (accept_3_2 118 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 147 272 (Polychromatic418967fa.accept_11_7_4_8_1_1371 117 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 147 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 116 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 147 272 (accept_3_2 115 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 114 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 147 272 (accept_3_2 112 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 147 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 111 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 147 272 (Polychromatic418967fa.accept_15_5_12_2_1_2820 110 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 147 272 (accept_3_2 109 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 147 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 108 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 147 272 (accept_3_2 106 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 147 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 104 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 147 272 (accept_3_2 103 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 147 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 102 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 147 272 (accept_3_2 100 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 147 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 99 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 147 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 147 272 (accept_3_2 97 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 147 272 (accept_3_2 94 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 147 272 (Polychromatic418967fa.accept_13_2_4_12_1_745 93 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 147 272 (Polychromatic418967fa.accept_14_8_7_6_1_1159 92 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 147 272 (accept_3_2 91 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 147 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 147 272 (accept_3_2 88 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 147 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 86 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 147 272 (accept_3_2 85 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 147 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 147 272 (accept_3_2 82 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 147 272 (Polychromatic418967fa.accept_13_3_4_12_1_36 81 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 147 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 147 272 (accept_3_2 79 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 147 272 (accept_3_2 76 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 147 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 75 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 147 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 147 272 (accept_3_2 73 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 147 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341 72 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 147 272 (accept_3_2 70 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 147 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 147 272 (accept_3_2 67 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 147 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 66 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 147 272 (accept_3_2 64 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 147 272 (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 147 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 147 272 (accept_3_2 61 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 60 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 147 272 (accept_3_2 58 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 147 272 (Polychromatic418967fa.accept_13_5_4_12_1_2058 57 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 147 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 147 272 (accept_3_2 55 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 147 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 54 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 147 272 (accept_3_2 52 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 51 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 147 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 147 272 (accept_3_2 49 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 147 272 (Polychromatic418967fa.accept_15_3_12_2_1_507 48 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 147 272 (accept_3_2 46 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 147 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 45 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 147 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 44 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 147 272 (accept_3_2 43 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 147 272 (accept_3_2 40 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 147 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 39 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 147 272 (Polychromatic418967fa.accept_27_11_12_2_1_16689 38 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 147 272 (accept_3_2 37 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 147 272 (Polychromatic418967fa.accept_14_8_7_6_1_1159 36 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 147 272 (accept_3_2 34 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 147 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 32 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 147 272 (accept_3_2 31 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 147 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 147 272 (accept_3_2 28 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 147 272 (Polychromatic418967fa.accept_14_13_7_6_1_3525 27 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 147 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 147 272 (accept_3_2 25 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 147 272 (accept_3_2 22 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 147 272 (Polychromatic418967fa.accept_13_8_4_12_1_2753 21 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 147 272 (Polychromatic418967fa.accept_13_7_4_12_1_1341 20 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 147 272 (accept_3_2 19 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 147 272 (Polychromatic418967fa.accept_11_7_4_8_1_1371 18 147
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 147 272 (accept_3_2 16 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 147 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 147 272 (accept_3_2 13 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 147 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 12 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 147 272 (accept_3_2 10 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  147 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 9 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 147 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 147 272 (accept_3_2 7 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 147 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 147 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 147 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 147 272 (accept_3_2 4 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  147 272 (Polychromatic418967fa.accept_13_3_4_12_1_36 3 147 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 147 272 (Polychromatic418967fa.accept_13_2_4_12_1_745 2 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 147 272 (accept_3_2 1 147 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 147
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 127 146 272 (Eq.refl Bool.true) (allA_succ_of_gcd 126 146 272 2 63 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 146 272
  (Polychromatic418967fa.accept_12_5_2_8_1_172 125 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 146 272 2 62 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 146 272 (Polychromatic418967fa.accept_19_9_13_6_1_7198 123 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 146 272 2 61 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 146 272 (accept_3_2 121 146 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 146 272 2 60 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 146 272
  (Polychromatic418967fa.accept_12_11_2_8_1_511 119 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 118 146 272 2 59 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 117 146 272 (Polychromatic418967fa.accept_20_17_6_12_1_8185 117 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 146 272 2 58 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 146 272 (accept_3_2 115 146 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 146 272 2 57 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 146 272
  (Polychromatic418967fa.accept_12_5_2_8_1_172 113 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 146 272 2 56 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 146 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 111 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 146 272 2 55 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 146 272 (accept_3_2 109 146 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 146 272 2 54 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 146 272
  (Polychromatic418967fa.accept_12_11_2_8_1_511 107 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 146 272 2 53 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 146 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 105 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 146 272 2 52 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 146 272 (accept_3_2 103 146 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 146 272 2 51 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 146 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 101 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 100 146 272 2 50 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 99 146 272 (Polychromatic418967fa.accept_15_9_11_2_1_1882 99 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 146 272 2 49 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 146 272 (accept_3_2 97 146 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 146 272 2 48 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 146 272
  (Polychromatic418967fa.accept_12_11_2_8_1_511 95 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 146 272 2 47 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 146 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 93 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 146 272 2 46 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 146 272 (accept_3_2 91 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 146 272 2 45 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 146 272 (Polychromatic418967fa.accept_12_5_2_8_1_172
  89 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 146 272 2 44 73 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 146 272
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 87 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 146 272 2 43 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 146 272 (accept_3_2 85 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 146 272 2 42 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 146 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 83 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 146 272 2 41 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 146 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 146 272 2 40 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 146 272 (accept_3_2 79 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 146 272 2 39 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 146 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 77 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 146 272 2 38 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 146 272
  (Polychromatic418967fa.accept_20_15_6_12_1_2446 75 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 74 146 272 2 37 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 73 146 272 (accept_3_2 73 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 146 272 2 36 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 146 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 146 272 2 35 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 146 272
  (Polychromatic418967fa.accept_13_4_3_12_1_2066 69 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 146 272 2 34 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 146 272 (accept_3_2 67 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 146 272 2 33 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 146 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 65 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 146 272 2 32 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 146 272
  (Polychromatic418967fa.accept_24_15_2_8_1_11685 63 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 146 272 2 31 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 146 272 (accept_3_2 61 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 146 272 2 30 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 146 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 59 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 146 272 2 29 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 146 272
  (Polychromatic418967fa.accept_20_17_6_12_1_8185 57 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 56 146 272 2 28 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 55 146 272 (accept_3_2 55 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 146 272 2 27 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 146 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 146 272 2 26 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 146 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 146 272 2 25 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 146 272 (accept_3_2 49 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 146 272 2 24 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 146 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 47 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 146 272 2 23 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 146 272
  (Polychromatic418967fa.accept_19_7_13_6_1_1914 45 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 146 272 2 22 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 146 272 (accept_3_2 43 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 146 272 2 21 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 146 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 146 272 2 20 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 146 272
  (Polychromatic418967fa.accept_11_6_3_8_1_843 39 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 146 272 2 19 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 146 272 (accept_3_2 37 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 146 272 2 18 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 146 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 146 272 2 17 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 146 272
  (Polychromatic418967fa.accept_22_11_14_8_1_12010 33 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 32 146 272 2 16 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 31 146 272 (accept_3_2 31 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 146 272 2 15 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 146 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 146 272 2 14 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 146 272
  (Polychromatic418967fa.accept_11_5_3_8_1_454 27 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 146 272 2 13 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 146 272 (accept_3_2 25 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 146 272 2 12 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 146 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 23 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 146 272 2 11 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 146 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 146 272 2 10 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 146 272 (accept_3_2 19 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 146 272 2 9 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 146 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 17 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 146 272 2 8 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 146 272
  (Polychromatic418967fa.accept_13_2_3_12_1_735 15 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 146 272 2 7 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 146 272 (accept_3_2 13 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 146 272 2 6 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 146 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 146 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 146 272 2 5 73 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 146 272
  (Polychromatic418967fa.accept_13_9_3_12_1_2025 9 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 146 272 2 4 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 146 272 (accept_3_2 7 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 146
  272 2 3 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  146 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 5 146 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 146 272 2 2 73 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 146 272 (Polychromatic418967fa.accept_24_3_2_8_1_4572 3 146 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 146 272 2 1 73 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 146 272 (accept_3_2 1 146 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 146
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 128 145 272 (Eq.refl Bool.true) (allA_of_3_0 128 145 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 129 144 272 (Eq.refl Bool.true) (allA_succ_of_gcd 128 144 272 16 8 9 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 144 272 (accept_3_2 127 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 144 272 2 63 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 144 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366
  125 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 144 272 4 31 36 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 144 272
  (Polychromatic418967fa.accept_25_23_19_22_1_16688 123 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 122 144 272 2 61 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 121 144 272 (accept_3_2 121 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 144 272 8 15 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 144 272 (Polychromatic418967fa.accept_13_2_1_12_1_1326 119 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 144 272 2 59 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 144 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 117 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 144 272 4 29 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 144 272 (accept_3_2 115 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 144 272 2 57 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 144 272 (Polychromatic418967fa.accept_15_8_9_2_1_1897 113 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 144 272 16 7 9 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 144 272
  (Polychromatic418967fa.accept_19_16_11_6_1_7149 111 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 144 272 2 55 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 144 272 (accept_3_2 109 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 144 272 4 27 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 144 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 107 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 144 272 2 53 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 144 272
  (Polychromatic418967fa.accept_23_13_6_19_1_10180 105 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 104 144 272 8 13 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 103 144 272 (accept_3_2 103 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 144 272 2 51 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 144 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 101 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 144 272 4 25 36 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 144 272
  (Polychromatic418967fa.accept_13_8_1_12_1_762 99 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 144 272 2 49 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 144 272 (accept_3_2 97 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 144 272 16 6 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 144 272 (Polychromatic418967fa.accept_21_11_18_20_1_1877 95 144 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 144 272 2 47 72 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 144 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 93 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 144 272 4 23 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 144 272 (accept_3_2 91 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 144 272 2 45 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 144 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 89 144 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 144 272 8 11 18 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 144 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 87 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 144 272 2 43 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 144 272 (accept_3_2 85 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 144 272 4 21 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 144 272 (Polychromatic418967fa.accept_13_5_1_12_1_740 83 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 144 272 2 41 72 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 144 272
  (Polychromatic418967fa.accept_11_4_1_8_1_1366 81 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 144 272 16 5 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 144 272 (accept_3_2 79 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78
  144 272 2 39 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 144 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 77 144 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 144 272 4 19 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 144 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 75
  144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 144 272 2 37 72 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 144 272 (accept_3_2 73
  144 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 144 272 8 9 18 34 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 144 272
  (Polychromatic418967fa.accept_15_11_9_2_1_4780 71 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 144 272 2 35 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 144 272 (Polychromatic418967fa.accept_21_6_18_20_1_6065 69 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 144 272 4 17 36 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 144 272 (accept_3_2 67 144 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 144 272 2 33 72 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 144 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 65 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 144 272 16 4 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 144 272 (Polychromatic418967fa.accept_13_11_1_12_1_742 63 144 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 144 272 2 31 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 144 272 (accept_3_2 61 144 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 60 144 272 4 15 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 144 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 144 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 144 272 2 29 72 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 144 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 57 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 144 272 8 7 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 144 272 (accept_3_2 55 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  144 272 2 27 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 144 272 (Polychromatic418967fa.accept_15_8_9_2_1_1897 53 144 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 144 272 4 13 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 144 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 51
  144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 144 272 2 25 72 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 144 272 (accept_3_2 49
  144 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 144 272 16 3 9 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 144 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 47 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 144 272 2 23 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 144 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 144 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 144 272 4 11 36 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 144 272 (accept_3_2 43 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 144 272 2 21 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 144 272 (Polychromatic418967fa.accept_13_2_1_12_1_1326
  41 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 144 272 8 5 18 34
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 144 272
  (Polychromatic418967fa.accept_19_1_11_6_1_7152 39 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 144 272 2 19 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 144 272 (accept_3_2 37 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 144 272 4 9 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 144 272 (Polychromatic418967fa.accept_19_16_11_6_1_7149 35 144 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 144 272 2 17 72 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 144 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 33 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 144 272 16 2 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 31 144 272 (accept_3_2 31 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30
  144 272 2 15 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 29 144 272 (Polychromatic418967fa.accept_22_7_12_8_1_4002 29 144 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 144 272 4 7 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 144 272 (Polychromatic418967fa.accept_10_7_4_2_1_903
  27 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 144 272 2 13 72 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 144 272
  (accept_3_2 25 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 144 272 8 3 18 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 144 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 23 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 22 144 272 2 11 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 21 144 272 (Polychromatic418967fa.accept_13_8_1_12_1_762 21 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 144 272 4 5 36 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 144 272 (accept_3_2 19 144 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 144 272 2 9 72 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 144 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 17 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 144 272 16 1 9 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 144 272 (Polychromatic418967fa.accept_11_4_1_8_1_1366 15 144 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 144 272 2 7 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 144 272 (accept_3_2 13 144 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 144 272 4 3 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 144 272 (Polychromatic418967fa.accept_13_11_1_12_1_742 11 144
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 144 272 2 5 72 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 144 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 9 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 144 272 8 1 18 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 144 272 (accept_3_2 7 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 144
  272 2 3 72 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  144 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 144 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 144 272 4 1 36 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 144 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 144 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 144 272 2 1 72 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 144 272 (accept_3_2 1 144 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 144
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 130 143 272 (Eq.refl Bool.true) (allA_succ_of_accept 129 143 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 129 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 128 143 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 128 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 143 272 (accept_3_2 127 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 143 272 (Polychromatic418967fa.accept_15_6_8_2_1_104 126 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 143 272
  (Polychromatic418967fa.accept_10_5_3_2_1_899 125 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 143 272 (accept_3_2 124 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 143 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 122 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 143 272 (accept_3_2 121 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 143 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 120 143
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 143 272
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 119 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 118 143 272 (accept_3_2 118 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 117 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 143 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 116 143
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 143 272 (accept_3_2 115 143
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 143 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 114 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 113 143 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 113 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 143 272 (accept_3_2 112 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 111 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 143 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 110 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 143 272 (accept_3_2 109 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 143 272 (Polychromatic418967fa.accept_14_10_3_6_1_2728 108 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 107 143 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 107 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 143 272 (accept_3_2 106 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 143
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 143 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 104 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 143 272 (accept_3_2 103 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 143 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 143 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 101 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 143 272 (accept_3_2 100 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 143 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 98 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 143 272 (accept_3_2 97 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 143 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 143 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 95 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 143 272 (accept_3_2 94 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 143 272
  (Polychromatic418967fa.accept_19_16_10_6_1_11403 92 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 91 143 272 (accept_3_2 91 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 90 143 272 (Polychromatic418967fa.accept_19_14_10_6_1_4372 90 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 143 272
  (Polychromatic418967fa.accept_19_13_10_6_1_7147 89 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 88 143 272 (accept_3_2 88 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 87 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 143 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 143 272 (accept_3_2 85 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 143 272 (Polychromatic418967fa.accept_9_3_8_2_1_162
  84 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 143 272
  (Polychromatic418967fa.accept_18_11_17_2_1_6349 83 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 82 143 272 (accept_3_2 82 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 81 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 143 272 (Polychromatic418967fa.accept_14_10_3_6_1_2728 80 143
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 143 272 (accept_3_2 79 143
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 143 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 78 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 77 143 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 143 272 (accept_3_2 76 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 75 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 143 272 (Polychromatic418967fa.accept_7_4_3_6_1_340
  74 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 143 272 (accept_3_2 73
  143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 143 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 72 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 143 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 71 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 143 272 (accept_3_2 70 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 143 272 (Polychromatic418967fa.accept_9_5_8_2_1_409
  68 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 143 272 (accept_3_2 67
  143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 143 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 66 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 143 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 65 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 143 272 (accept_3_2 64 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 143 272 (Polychromatic418967fa.accept_12_2_11_8_1_504
  62 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 143 272 (accept_3_2 61
  143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 143 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 60 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 143 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 143 272 (accept_3_2 58 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 143 272
  (Polychromatic418967fa.accept_21_14_17_20_1_12259 56 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 55 143 272 (accept_3_2 55 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 54 143 272 (Polychromatic418967fa.accept_15_9_8_2_1_1109 54 143 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 143 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 53 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 143 272 (accept_3_2 52 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51
  143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 143 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 143 272 (accept_3_2 49 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 143 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 143 272 (Polychromatic418967fa.accept_18_11_17_2_1_6349 47 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 143 272 (accept_3_2 46 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 143 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 44 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 143 272 (accept_3_2 43 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 143 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 143 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 143 272 (accept_3_2 40 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 143 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 38 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 143 272 (accept_3_2 37 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 143 272 (Polychromatic418967fa.accept_15_6_8_2_1_104 36 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 143 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 35 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 143 272 (accept_3_2 34 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 143 272
  (Polychromatic418967fa.accept_7_4_3_6_1_340 32 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 143 272 (accept_3_2 31 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 143 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 143 272 (Polychromatic418967fa.accept_18_11_17_2_1_6349 29 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 143 272 (accept_3_2 28 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 143 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 26 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 143 272 (accept_3_2 25 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 143 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 143 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 23 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 143 272 (accept_3_2 22 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 143 272
  (Polychromatic418967fa.accept_19_1_10_6_1_5726 20 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 143 272 (accept_3_2 19 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 143 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 143 272 (Polychromatic418967fa.accept_25_17_18_22_1_14967 17 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 143 272 (accept_3_2 16 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 143 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 143 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 143 272 (accept_3_2 13 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 143 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 143 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 11 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 143 272 (accept_3_2 10 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 9 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 143 272
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 8 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 143 272 (accept_3_2 7 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  143 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 143 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 143 272 (accept_3_2 4 143 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 143 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 143 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 143 272
  (Polychromatic418967fa.accept_7_2_3_6_1_4 2 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 143 272 (accept_3_2 1 143 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 143
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 131 142 272 (Eq.refl Bool.true) (allA_of_3_0 131 142 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 132 141 272 (Eq.refl Bool.true) (allA_succ_of_accept 131 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 131 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 141 272 (accept_3_2 130 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 129 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 128 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 141 272 (accept_3_2 127 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 141 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 126 141
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 141 272 (accept_3_2 124 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 141 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 123 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 141 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 122 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 141 272 (accept_3_2 121 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 120 141
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 141 272 (accept_3_2 118 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 117 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 141 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 116 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 141 272 (accept_3_2 115 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 114 141
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 141 272 (accept_3_2 112 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 111 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 110 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 141 272 (accept_3_2 109 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 141 272 (Polychromatic418967fa.accept_13_4_11_12_1_1318 108
  141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 141 272 (accept_3_2 106 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 141 272 (Polychromatic418967fa.accept_13_1_11_12_1_1322 105 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 104 141 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 104 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 141 272 (accept_3_2 103 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 141
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 141 272 (accept_3_2 100 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 141 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 99 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 141 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 141 272 (accept_3_2 97 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 96 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 141 272 (accept_3_2 94 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 93 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 141 272 (Polychromatic418967fa.accept_13_1_11_12_1_1322 92 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 141 272 (accept_3_2 91 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 141 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 141
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 141 272 (accept_3_2 88 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 141 272 (Polychromatic418967fa.accept_11_10_9_8_1_1974 87 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 86 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 141 272 (accept_3_2 85 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 141 272 (accept_3_2 82 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 141 272 (Polychromatic418967fa.accept_21_18_15_20_1_6076 81 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 80 141 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 80 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 141 272 (accept_3_2 79 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 78 141 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 78 141
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 141 272 (accept_3_2 76 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 75 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 141 272 (Polychromatic418967fa.accept_19_17_8_6_1_7146 74 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 141 272 (accept_3_2 73 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 72 141 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 141 272 (accept_3_2 70 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 141 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 69 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 68 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 141 272 (accept_3_2 67 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 66 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 141 272 (accept_3_2 64 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 141 272 (Polychromatic418967fa.accept_10_3_1_2_1_521 63 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 141 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 141 272 (accept_3_2 61 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 141 272 (Polychromatic418967fa.accept_19_3_8_6_1_4368 60 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 141 272 (accept_3_2 58 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 141 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 141 272 (accept_3_2 55 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 54 141 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 141 272 (accept_3_2 52 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 51 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 141 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 141 272 (accept_3_2 49 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 141 272 (accept_3_2 46 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 141 272 (Polychromatic418967fa.accept_19_7_8_6_1_3123 45 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 44 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 141 272 (accept_3_2 43 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 141 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 42 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 141 272 (accept_3_2 40 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 141 272 (Polychromatic418967fa.accept_15_8_6_2_1_1128 38 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 141 272 (accept_3_2 37 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 141 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 36 141
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 141 272 (accept_3_2 34 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 33 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 141 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 141 272 (accept_3_2 31 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 30 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 141 272 (accept_3_2 28 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 141 272 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 26 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 141 272 (accept_3_2 25 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 141 272 (Polychromatic418967fa.accept_25_24_16_22_1_14938 24 141 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 141 272 (accept_3_2 22 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 141 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 20 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 141 272 (accept_3_2 19 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 141 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 18 141
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 141 272 (accept_3_2 16 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 141 272 (Polychromatic418967fa.accept_24_15_21_8_1_11704 15 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 14 141 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 141 272 (accept_3_2 13 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 141 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 12 141 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 141 272 (accept_3_2 10 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 9 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 141 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 141 272 (accept_3_2 7 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 141 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 6 141 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 141 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 141 272 (accept_3_2 4 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  141 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 141 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 141 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 2 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 141 272 (accept_3_2 1 141 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 141
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 133 140 272 (Eq.refl Bool.true) (allA_succ_of_gcd 132 140 272 4 33 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 140 272
  (Polychromatic418967fa.accept_15_11_5_2_1_520 131 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 130 140 272 2 65 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 129 140 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 129 140 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 140 272 4 32 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 140 272 (accept_3_2 127 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 140 272 2 63 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 140 272 (Polychromatic418967fa.accept_9_8_5_2_1_422
  125 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 140 272 4 31 35 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 140 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 123 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 140 272 2 61 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 140 272 (accept_3_2 121 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 140 272 4 30 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 140 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 119 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 140 272 2 59 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 140 272
  (Polychromatic418967fa.accept_15_12_5_2_1_2786 117 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 140 272 4 29 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 140 272 (accept_3_2 115 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 140 272 2 57 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 140 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 113 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 140 272 4 28 35 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 140 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 111 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 140 272 2 55 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 140 272 (accept_3_2 109 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 140 272 4 27 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 140 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 107 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 140 272 2 53 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 140 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 105 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 140 272 4 26 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 140 272 (accept_3_2 103 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 140 272 2 51 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 140 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 101 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 140 272 4 25 35 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 140 272
  (Polychromatic418967fa.accept_13_8_10_12_1_1337 99 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 98 140 272 2 49 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 97 140 272 (accept_3_2 97 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 140 272 4 24 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 140 272 (Polychromatic418967fa.accept_21_11_14_20_1_12235 95 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 140 272 2 47 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 140 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 93 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 140 272 4 23 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 140 272 (accept_3_2 91 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 140 272 2 45 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 140 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 89 140 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 140 272 4 22 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 140 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 87 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 140 272 2 43 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 140 272 (accept_3_2 85 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 140 272 4 21 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 140 272 (Polychromatic418967fa.accept_18_11_14_2_1_5058 83 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 140 272 2 41 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 140 272
  (Polychromatic418967fa.accept_19_5_7_6_1_11379 81 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 140 272 4 20 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 140 272 (accept_3_2 79 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 140 272 2 39 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 140 272 (Polychromatic418967fa.accept_19_1_7_6_1_1959 77 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 140 272 4 19 35 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 140 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 75 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 140 272 2 37 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 140 272 (accept_3_2 73 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 140 272 4 18 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 140 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 71 140 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 140 272 2 35 70 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 140 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 69 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 140 272 4 17 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 140 272 (accept_3_2 67 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 140 272 2 33 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 140 272 (Polychromatic418967fa.accept_18_11_14_2_1_5058 65 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 140 272 4 16 35 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 140 272
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 63 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 140 272 2 31 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 140 272 (accept_3_2 61 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 140 272 4 15 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 140 272 (Polychromatic418967fa.accept_13_7_10_12_1_2047 59 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 140 272 2 29 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 140 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 57 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 140 272 4 14 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 140 272 (accept_3_2 55 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 140 272 2 27 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 140 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 53 140 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 140 272 4 13 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 140 272
  (Polychromatic418967fa.accept_9_6_5_2_1_421 51 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 140 272 2 25 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 140 272 (accept_3_2 49 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 140 272 4 12 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 140 272 (Polychromatic418967fa.accept_13_8_10_12_1_1337 47 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 140 272 2 23 70 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 140 272
  (Polychromatic418967fa.accept_13_6_10_12_1_2049 45 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 44 140 272 4 11 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 43 140 272 (accept_3_2 43 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 140 272 2 21 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 140 272 (Polychromatic418967fa.accept_13_2_10_12_1_757 41 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 140 272 4 10 35 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 140 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 39 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 140 272 2 19 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 140 272 (accept_3_2 37 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 140 272 4 9 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 140 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 35 140 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 140 272 2 17 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 140 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 33
  140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 140 272 4 8 35 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 140 272 (accept_3_2 31
  140 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 140 272 2 15 70 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 140 272
  (Polychromatic418967fa.accept_15_14_5_2_1_4761 29 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 140 272 4 7 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 140 272 (Polychromatic418967fa.accept_15_12_5_2_1_2786 27 140 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 140 272 2 13 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 140 272 (accept_3_2 25 140 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 140 272 4 6 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 140 272 (Polychromatic418967fa.accept_21_2_14_20_1_841 23 140
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 140 272 2 11 70 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 140 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 21 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 140 272 4 5 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 140 272 (accept_3_2 19 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  140 272 2 9 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 140 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 17 140 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 140 272 4 4 35 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 140 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 15
  140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 140 272 2 7 70 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 140 272 (accept_3_2 13
  140 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 12 140 272 4 3 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 140 272
  (Polychromatic418967fa.accept_13_11_10_12_1_1338 11 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 10 140 272 2 5 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 9 140 272 (Polychromatic418967fa.accept_13_9_10_12_1_2048 9 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 8 140 272 4 2 35 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 7 140 272 (accept_3_2 7 140 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 140 272 2 3 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5 140 272 (Polychromatic418967fa.accept_19_5_7_6_1_11379
  5 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 4 140 272 4 1 35 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 3 140 272
  (Polychromatic418967fa.accept_9_3_5_2_1_28 3 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 2 140 272 2 1 70 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 1 140 272 (accept_3_2 1 140 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 140
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 134 139 272 (Eq.refl Bool.true) (allA_of_3_0 134 139 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allB_succ' 135 138 272 (Eq.refl Bool.true) (allA_succ_of_gcd 134 138 272 2 67 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 133 138 272 (accept_3_2 133 138 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 132 138 272 2 66 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 131 138 272 (Polychromatic418967fa.accept_9_5_3_2_1_171
  131 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 138 272 2 65 69 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 138 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 129 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 138 272 2 64 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 138 272 (accept_3_2 127 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 138 272 2 63 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 138 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 125 138 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 138 272 2 62 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 138 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 123 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 138 272 2 61 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 138 272 (accept_3_2 121 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 138 272 2 60 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 138 272 (Polychromatic418967fa.accept_15_14_3_2_1_2811 119 138 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 138 272 2 59 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 138 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 117 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 138 272 2 58 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 138 272 (accept_3_2 115 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 138 272 2 57 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 138 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 113 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 138 272 2 56 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 138 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 111 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 138 272 2 55 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 138 272 (accept_3_2 109 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 138 272 2 54 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 138 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 107 138 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 138 272 2 53 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 138 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 105 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 138 272 2 52 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 138 272 (accept_3_2 103 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 138 272 2 51 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 138 272 (Polychromatic418967fa.accept_13_10_8_12_1_2032 101 138 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 138 272 2 50 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 138 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 99 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 138 272 2 49 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 138 272 (accept_3_2 97 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 138 272 2 48 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 138 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 95 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 138 272 2 47 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 138 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 138 272 2 46 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 138 272 (accept_3_2 91 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 138 272 2 45 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 138 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 89 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 138 272 2 44 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 138 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 87 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 138 272 2 43 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 138 272 (accept_3_2 85 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 138 272 2 42 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 138 272 (Polychromatic418967fa.accept_13_5_8_12_1_2759 83 138 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 138 272 2 41 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 138 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 81 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 138 272 2 40 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 138 272 (accept_3_2 79 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 138 272 2 39 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 138 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 77 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 138 272 2 38 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 138 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 75 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 138 272 2 37 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 138 272 (accept_3_2 73 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 138 272 2 36 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 138 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 138 272 2 35 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 138 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 69 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 138 272 2 34 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 138 272 (accept_3_2 67 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 138 272 2 33 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 138 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 65 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 138 272 2 32 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 138 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 138 272 2 31 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 138 272 (accept_3_2 61 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 138 272 2 30 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 138 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 59 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 138 272 2 29 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 138 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 57 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 138 272 2 28 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 138 272 (accept_3_2 55 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 138 272 2 27 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 138 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 53 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 138 272 2 26 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 138 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 51 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 138 272 2 25 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 138 272 (accept_3_2 49 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 138 272 2 24 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 138 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 47 138 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 138 272 2 23 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 138 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 45 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 138 272 2 22 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 138 272 (accept_3_2 43 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 138 272 2 21 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 138 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 41 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 138 272 2 20 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 138 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 39 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 138 272 2 19 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 138 272 (accept_3_2 37 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 138 272 2 18 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 138 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 35 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 138 272 2 17 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 138 272
  (Polychromatic418967fa.accept_9_6_3_2_1_431 33 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 138 272 2 16 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 138 272 (accept_3_2 31 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 138 272 2 15 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 138 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 29 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 138 272 2 14 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 138 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 138 272 2 13 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 138 272 (accept_3_2 25 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 138 272 2 12 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 138 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 23 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 138 272 2 11 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 138 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 21 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 138 272 2 10 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 138 272 (accept_3_2 19 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 138 272 2 9 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 138 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 17 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 138 272 2 8 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 138 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 15 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 138 272 2 7 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 138 272 (accept_3_2 13 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 138 272 2 6 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 138 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 11 138 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 138 272 2 5 69 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 138 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 138 272 2 4 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 138 272 (accept_3_2 7 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 138
  272 2 3 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  138 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 5 138 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 138 272 2 2 69 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 138 272 (Polychromatic418967fa.accept_11_3_6_8_1_1924 3 138 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 138 272 2 1 69 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 138 272 (accept_3_2 1 138 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 138
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ' 136 137 272 (Eq.refl Bool.true) (allA_succ_of_accept 135 137 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 135 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 134 137 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 134 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 137 272 (accept_3_2 133 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 137 272 (Polychromatic418967fa.accept_21_6_11_20_1_10794 132 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 137 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 131 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 137 272 (accept_3_2 130 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 129 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 137 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 128 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 137 272 (accept_3_2 127 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 137 272 (Polychromatic418967fa.accept_19_12_4_6_1_7163 126
  137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 137 272
  (Polychromatic418967fa.accept_10_5_7_2_1_516 125 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 137 272 (accept_3_2 124 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 137 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 122 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 137 272 (accept_3_2 121 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 137 272 (Polychromatic418967fa.accept_22_10_5_8_1_8954 120
  137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 137 272
  (Polychromatic418967fa.accept_10_9_7_2_1_887 119 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 137 272 (accept_3_2 118 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 137 272 (Polychromatic418967fa.accept_19_2_4_6_1_5738 116 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 137 272 (accept_3_2 115 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 137 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 114 137
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 137 272
  (Polychromatic418967fa.accept_11_3_5_8_1_458 113 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 137 272 (accept_3_2 112 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 137 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 110 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 137 272 (accept_3_2 109 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 137 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 108 137
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 137 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 107 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 137 272 (accept_3_2 106 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 137 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 104 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 137 272 (accept_3_2 103 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 137 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 102 137
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 137 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 101 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 137 272 (accept_3_2 100 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 137 272 (Polychromatic418967fa.accept_12_2_5_8_1_159 98 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 137 272 (accept_3_2 97 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 137 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 137 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 137 272
  (Polychromatic418967fa.accept_10_5_7_2_1_516 95 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 137 272 (accept_3_2 94 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 137 272 (Polychromatic418967fa.accept_21_8_11_20_1_4574 92 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 137 272 (accept_3_2 91 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 137 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 90 137
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 137 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 89 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 137 272 (accept_3_2 88 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 137 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 137 272 (accept_3_2 85 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 137 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 84 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 137 272
  (Polychromatic418967fa.accept_13_5_7_12_1_2757 83 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 137 272 (accept_3_2 82 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 137 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 137 272 (accept_3_2 79 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 137 272 (Polychromatic418967fa.accept_19_2_4_6_1_5738 78 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 137 272
  (Polychromatic418967fa.accept_21_14_11_20_1_12301 77 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 137 272 (accept_3_2 76 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 137 272 (Polychromatic418967fa.accept_10_4_7_2_1_211 74 137
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 137 272 (accept_3_2 73 137
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 137 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 72 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 71 137 272 (Polychromatic418967fa.accept_13_6_7_12_1_3504 71 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 137 272 (accept_3_2 70 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 69 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 137 272 (Polychromatic418967fa.accept_7_5_4_6_1_167
  68 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 137 272 (accept_3_2 67
  137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 137 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 66 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 65 137 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 65 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 137 272 (accept_3_2 64 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 63 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 137 272 (Polychromatic418967fa.accept_12_2_5_8_1_159
  62 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 137 272 (accept_3_2 61
  137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 137 272
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 60 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 59 137 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 59 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 137 272 (accept_3_2 58 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 57 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 137 272
  (Polychromatic418967fa.accept_13_4_7_12_1_2823 56 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 137 272 (accept_3_2 55 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 137 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 137 272 (Polychromatic418967fa.accept_18_17_11_2_1_7782 53 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 137 272 (accept_3_2 52 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 51 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 137 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 137 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 50 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 137 272 (accept_3_2 49 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 137 272 (Polychromatic418967fa.accept_19_10_4_6_1_11376 48 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 137 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 47 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 137 272 (accept_3_2 46 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 45 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 137 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 44 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 137 272 (accept_3_2 43 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 137 272 (Polychromatic418967fa.accept_20_2_17_12_1_5178 42 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 137 272 (Polychromatic418967fa.accept_19_3_4_6_1_9976 41 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 137 272 (accept_3_2 40 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 39 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 137 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 137 272
  (Polychromatic418967fa.accept_7_3_4_6_1_329 38 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 137 272 (accept_3_2 37 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 137 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 36 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 137 272 (Polychromatic418967fa.accept_10_5_7_2_1_516 35 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 137 272 (accept_3_2 34 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 137 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 137 272
  (Polychromatic418967fa.accept_13_6_7_12_1_3504 32 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 137 272 (accept_3_2 31 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 137 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 137 272 (Polychromatic418967fa.accept_10_9_7_2_1_887 29 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 137 272 (accept_3_2 28 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 137 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 137 272
  (Polychromatic418967fa.accept_7_5_4_6_1_167 26 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 137 272 (accept_3_2 25 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 137 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 137 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 23 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 137 272 (accept_3_2 22 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 137 272
  (Polychromatic418967fa.accept_23_20_22_19_1_16687 20 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 19 137 272 (accept_3_2 19 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 18 137 272 (Polychromatic418967fa.accept_13_5_7_12_1_2757 18 137 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 137 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 17 137 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 137 272 (accept_3_2 16 137 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15
  137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 137 272
  (Polychromatic418967fa.accept_10_4_7_2_1_211 14 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 137 272 (accept_3_2 13 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 137 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 137 272 (Polychromatic418967fa.accept_13_11_7_12_1_2758 11 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 137 272 (accept_3_2 10 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 137 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 137 272
  (Polychromatic418967fa.accept_13_8_7_12_1_3637 8 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 137 272 (accept_3_2 7 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  137 272 (Polychromatic418967fa.accept_13_6_7_12_1_3504 6 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 137 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 5 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 137 272 (accept_3_2 4 137 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 137 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 137 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 137 272
  (Polychromatic418967fa.accept_7_2_4_6_1_166 2 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 137 272 (accept_3_2 1 137 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 137
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 136 272 (allA_of_3_0 136 136 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 135 272
  (allA_succ_of_accept 134 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 134 135 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 133 135 272 (accept_3_2 133 135 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 132 135 272 (Polychromatic418967fa.accept_13_2_5_12_1_2043 132 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 131 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 131 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 130 135 272 (accept_3_2 130 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  129 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 129 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 128 135 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 128 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 135 272 (accept_3_2 127 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 135 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 126 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 135 272 (accept_3_2 124 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 123 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 122 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 135 272 (accept_3_2 121 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 120 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 135 272 (accept_3_2 118 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 135 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 117 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 116 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 135 272 (accept_3_2 115 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 135 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 114 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 135 272 (accept_3_2 112 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 135 272 (Polychromatic418967fa.accept_13_7_5_12_1_1305 111 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 110 135 272 (Polychromatic418967fa.accept_13_6_5_12_1_307 110 135 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 135 272 (accept_3_2 109 135 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56
  108 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 135 272 (accept_3_2 106 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 135 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 105 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 135 272 (Polychromatic418967fa.accept_11_5_3_8_1_454 104 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 135 272 (accept_3_2 103 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 102 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 135 272 (accept_3_2 100 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 99 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 135 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 98 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 135 272 (accept_3_2 97 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 135 272 (Polychromatic418967fa.accept_18_6_9_2_1_1575 96 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 135 272 (accept_3_2 94 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 135 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 93 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 92 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 135 272 (accept_3_2 91 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 90 135 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 135 272 (accept_3_2 88 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 135 272 (Polychromatic418967fa.accept_13_8_5_12_1_2755 86 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 135 272 (accept_3_2 85 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 135 272 (Polychromatic418967fa.accept_13_6_5_12_1_307 84 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 135 272 (accept_3_2 82 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 81 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 80 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 135 272 (accept_3_2 79 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 78 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 135 272 (accept_3_2 76 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 135 272 (Polychromatic418967fa.accept_18_3_9_2_1_5053 75 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 74 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 135 272 (accept_3_2 73 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 135 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 72 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 135 272 (accept_3_2 70 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 135 272 (Polychromatic418967fa.accept_13_4_5_12_1_751 69 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 135 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 68 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 135 272 (accept_3_2 67 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 66 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 66 135 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 135 272 (accept_3_2 64 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 135 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 63 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 135 272 (Polychromatic418967fa.accept_23_16_20_19_1_16686 62 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 135 272 (accept_3_2 61 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 60 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 60 135 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 135 272 (accept_3_2 58 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 57 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 135 272 (Polychromatic418967fa.accept_13_4_5_12_1_751 56 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 135 272 (accept_3_2 55 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 135 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 54 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 135 272 (accept_3_2 52 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 135 272 (Polychromatic418967fa.accept_19_13_2_6_1_13962 51 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 50 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 135 272 (accept_3_2 49 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 135 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 48 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 135 272 (accept_3_2 46 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 135 272 (Polychromatic418967fa.accept_21_2_9_20_1_9260 44 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 135 272 (accept_3_2 43 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 42 135 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 135 272 (accept_3_2 40 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 38 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 135 272 (accept_3_2 37 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 36 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 135 272 (accept_3_2 34 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 135 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 33 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 32 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 135 272 (accept_3_2 31 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 135 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 30 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 135 272 (accept_3_2 28 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 135 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 27 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 135 272 (Polychromatic418967fa.accept_20_6_15_12_1_6637 26 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 135 272 (accept_3_2 25 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 24 135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 24 135 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 135 272 (accept_3_2 22 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 135 272 (Polychromatic418967fa.accept_13_8_5_12_1_2755 21 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 135 272 (Polychromatic418967fa.accept_13_7_5_12_1_1305 20 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 135 272 (accept_3_2 19 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 135 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 18 135 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 135 272 (accept_3_2 16 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 135 272 (Polychromatic418967fa.accept_13_1_5_12_1_306 14 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 135 272 (accept_3_2 13 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 135 272 (Polychromatic418967fa.accept_19_12_2_6_1_9981 12 135
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 135 272 (accept_3_2 10 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  135 272 (Polychromatic418967fa.accept_25_9_10_22_1_16685 9 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 135 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 8 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 135 272 (accept_3_2 7 135 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 135 272 (Polychromatic418967fa.accept_11_6_3_8_1_843 6 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 135 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 135 272 (accept_3_2 4 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  135 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 135 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 135 272 (Polychromatic418967fa.accept_13_2_5_12_1_2043 2 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 135 272 (accept_3_2 1 135 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 135
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 134 272 (allA_succ_of_accept 133 134 272 (accept_3_2 133 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 132 134 272 2 66 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 131 134 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 131 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 134 272 2 65 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 134 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 129 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 128 134 272 2 64 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 127 134 272 (accept_3_2 127 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 134 272 2 63 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 134 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 125 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 134 272 2 62 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 134 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 123 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 134 272 2 61 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 134 272 (accept_3_2 121 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 134 272 2 60 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 134 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 119 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 134 272 2 59 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 134 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 117 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 134 272 2 58 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 134 272 (accept_3_2 115 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 134 272 2 57 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 134 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 113 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 134 272 2 56 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 134 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 111 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 134 272 2 55 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 134 272 (accept_3_2 109 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 134 272 2 54 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 134 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 107 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 134 272 2 53 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 134 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 105 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 134 272 2 52 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 134 272 (accept_3_2 103 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 134 272 2 51 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 134 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 101 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 134 272 2 50 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 134 272
  (Polychromatic418967fa.accept_13_8_4_12_1_2753 99 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 134 272 2 49 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 134 272 (accept_3_2 97 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 134 272 2 48 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 134 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 134 272 2 47 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 134 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 93 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 134 272 2 46 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 134 272 (accept_3_2 91 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 134 272 2 45 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 134 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 89 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 134 272 2 44 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 134 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 87 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 134 272 2 43 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 134 272 (accept_3_2 85 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 134 272 2 42 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 134 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 83 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 134 272 2 41 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 134 272
  (Polychromatic418967fa.accept_13_3_4_12_1_36 81 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 134 272 2 40 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 134 272 (accept_3_2 79 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 134 272 2 39 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 134 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 134 272 2 38 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 134 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 75 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 134 272 2 37 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 134 272 (accept_3_2 73 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 134 272 2 36 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 134 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 71 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 134 272 2 35 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 134 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 69 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 134 272 2 34 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 134 272 (accept_3_2 67 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 134 272 2 33 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 134 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 65 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 134 272 2 32 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 134 272
  (Polychromatic418967fa.accept_13_11_4_12_1_3585 63 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 62 134 272 2 31 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 61 134 272 (accept_3_2 61 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 134 272 2 30 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 134 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 134 272 2 29 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 134 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 57 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 134 272 2 28 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 134 272 (accept_3_2 55 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 134 272 2 27 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 134 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 53 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 134 272 2 26 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 134 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 51 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 134 272 2 25 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 134 272 (accept_3_2 49 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 134 272 2 24 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 134 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 47 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 134 272 2 23 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 134 272
  (Polychromatic418967fa.accept_19_7_1_6_1_11374 45 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 134 272 2 22 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 134 272 (accept_3_2 43 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 134 272 2 21 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 134 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 134 272 2 20 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 134 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 39 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 134 272 2 19 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 134 272 (accept_3_2 37 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 134 272 2 18 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 134 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 35 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 134 272 2 17 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 134 272
  (Polychromatic418967fa.accept_7_5_1_6_1_163 33 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 134 272 2 16 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 134 272 (accept_3_2 31 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 134 272 2 15 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 134 272 (Polychromatic418967fa.accept_12_5_2_8_1_172 29 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 134 272 2 14 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 134 272
  (Polychromatic418967fa.accept_10_7_4_2_1_903 27 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 134 272 2 13 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 134 272 (accept_3_2 25 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 134 272 2 12 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 134 272 (Polychromatic418967fa.accept_7_2_1_6_1_173 23 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 134 272 2 11 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 134 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 21 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 134 272 2 10 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 134 272 (accept_3_2 19 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 134 272 2 9 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 134 272 (Polychromatic418967fa.accept_10_7_4_2_1_903 17 134 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 134 272 2 8 67 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 134 272
  (Polychromatic418967fa.accept_9_6_8_2_1_410 15 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 134 272 2 7 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 134 272 (accept_3_2 13 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 134 272 2 6 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 134 272 (Polychromatic418967fa.accept_12_11_2_8_1_511 11 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 134 272 2 5 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 134 272
  (Polychromatic418967fa.accept_7_2_1_6_1_173 9 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 134 272 2 4 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 134 272 (accept_3_2 7 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 134
  272 2 3 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  134 272 (Polychromatic418967fa.accept_7_5_1_6_1_163 5 134 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 134 272 2 2 67 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 134 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 3 134 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 134 272 2 1 67 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 134 272 (accept_3_2 1 134 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 134
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 133 272 (allA_of_3_0 133 133 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 132 272
  (allA_succ_of_accept 131 132 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 131 132 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 130 132 272 2 65 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 129 132 272 (Polychromatic418967fa.accept_9_3_6_2_1_160
  129 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 128 132 272 4 32 33 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 127 132 272
  (accept_3_2 127 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 126 132 272 2 63 66 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 125 132 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 125 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 124 132 272 4 31 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 123 132 272 (Polychromatic418967fa.accept_13_6_2_12_1_2802 123 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 122 132 272 2 61 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 121 132 272 (accept_3_2 121 132 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 120 132 272 4 30 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 119 132 272
  (Polychromatic418967fa.accept_15_14_12_2_1_3804 119 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 118 132 272 2 59 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 117 132 272 (Polychromatic418967fa.accept_18_9_6_2_1_2619 117 132 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 116 132 272 4 29 33 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 115 132 272 (accept_3_2
  115 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 114 132 272 2 57 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 113 132 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 113 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 112 132 272 4 28 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 111 132 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 111 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 110 132 272 2 55 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 109 132 272 (accept_3_2 109 132 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 108 132 272 4 27 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 107 132 272
  (Polychromatic418967fa.accept_9_8_6_2_1_744 107 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 106 132 272 2 53 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 105 132 272 (Polychromatic418967fa.accept_13_1_2_12_1_1299 105 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 104 132 272 4 26 33 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 103 132 272 (accept_3_2 103 132 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 102 132 272 2 51 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 101 132 272
  (Polychromatic418967fa.accept_13_10_2_12_1_1332 101 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 100 132 272 4 25 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 99 132 272 (Polychromatic418967fa.accept_18_9_6_2_1_2619 99 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 98 132 272 2 49 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 97 132 272 (accept_3_2 97 132 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 96 132 272 4 24 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 95 132 272
  (Polychromatic418967fa.accept_9_5_6_2_1_161 95 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 94 132 272 2 47 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 93 132 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 93 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 132 272 4 23 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 132 272 (accept_3_2 91 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 132 272 2 45 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 132 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 89
  132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 132 272 4 22 33 68 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 132 272
  (Polychromatic418967fa.accept_19_11_18_6_1_3113 87 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 86 132 272 2 43 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 85 132 272 (accept_3_2 85 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 132 272 4 21 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 132 272 (Polychromatic418967fa.accept_13_5_2_12_1_1301 83 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 132 272 2 41 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 132 272
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 81 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 132 272 4 20 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 132 272 (accept_3_2 79 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 132 272 2 39 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 132 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 77 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 132 272 4 19 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 132 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 75 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 132 272 2 37 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 132 272 (accept_3_2 73 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 132 272 4 18 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 132 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 71 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 132 272 2 35 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 132 272
  (Polychromatic418967fa.accept_13_4_2_12_1_2800 69 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 132 272 4 17 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 132 272 (accept_3_2 67 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 132 272 2 33 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 132 272 (Polychromatic418967fa.accept_15_5_12_2_1_2820 65 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 132 272 4 16 33 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 132 272
  (Polychromatic418967fa.accept_15_3_12_2_1_507 63 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 132 272 2 31 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 132 272 (accept_3_2 61 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 132 272 4 15 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 132 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 59 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 132 272 2 29 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 132 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 57 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 132 272 4 14 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 132 272 (accept_3_2 55 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 132 272 2 27 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 132 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 53 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 132 272 4 13 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 132 272
  (Polychromatic418967fa.accept_15_6_12_2_1_2803 51 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 132 272 2 25 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 132 272 (accept_3_2 49 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 132 272 4 12 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 132 272 (Polychromatic418967fa.accept_19_9_18_6_1_5778 47 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 132 272 2 23 66 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 132 272
  (Polychromatic418967fa.accept_13_6_2_12_1_2802 45 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 132 272 4 11 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 132 272 (accept_3_2 43 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 132 272 2 21 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 132 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 41 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 132 272 4 10 33 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 132 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 39 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 132 272 2 19 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 132 272 (accept_3_2 37 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 132 272 4 9 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 35 132 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 35 132 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 132 272 2 17 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 132 272 (Polychromatic418967fa.accept_15_3_12_2_1_507
  33 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 132 272 4 8 33 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 132 272
  (accept_3_2 31 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 132 272 2 15 66 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 132 272
  (Polychromatic418967fa.accept_13_3_2_12_1_2797 29 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 132 272 4 7 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 132 272 (Polychromatic418967fa.accept_13_1_2_12_1_1299 27 132 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 132 272 2 13 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 132 272 (accept_3_2 25 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 24 132 272 4 6 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 132 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 23 132 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 132 272 2 11 66 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 132 272
  (Polychromatic418967fa.accept_9_3_6_2_1_160 21 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 132 272 4 5 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 19 132 272 (accept_3_2 19 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18
  132 272 2 9 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 17 132 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 17 132 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 132 272 4 4 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 132 272
  (Polychromatic418967fa.accept_21_15_6_20_1_12272 15 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 14 132 272 2 7 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 13 132 272 (accept_3_2 13 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 132 272 4 3 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 11 132 272 (Polychromatic418967fa.accept_19_11_18_6_1_3113 11 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 132 272 2 5 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 132 272
  (Polychromatic418967fa.accept_18_9_6_2_1_2619 9 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 132 272 4 2 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 132 272 (accept_3_2 7 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 132
  272 2 3 66 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  132 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 5 132 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 132 272 4 1 33 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 132 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 3 132 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 132 272 2 1 66 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 132 272 (accept_3_2 1 132 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 132
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 131 272 (allA_succ_of_accept 130 131 272 (accept_3_2 130 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 129 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 129 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 128 131 272 (Polychromatic418967fa.accept_13_11_1_12_1_742 128
  131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 131 272 (accept_3_2 127
  131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 126 131 272
  (Polychromatic418967fa.accept_10_6_1_2_1_874 126 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 125 131 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 125 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 124 131 272 (accept_3_2 124 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 123 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 131 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 122 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 121 131 272 (accept_3_2 121 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  120 131 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 120 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 119 131 272 (Polychromatic418967fa.accept_10_9_1_2_1_522 119 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 131 272 (accept_3_2 118 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 117 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 131
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 131 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 116 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 131 272 (accept_3_2 115 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 131 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 114 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 131 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 113 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 131 272 (accept_3_2 112 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 131
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 131 272
  (Polychromatic418967fa.accept_12_2_11_8_1_504 110 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 131 272 (accept_3_2 109 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 131 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 108 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 131 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 107 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 131 272 (accept_3_2 106 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 131
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 131 272
  (Polychromatic418967fa.accept_19_9_17_6_1_3108 104 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 103 131 272 (accept_3_2 103 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 102 131 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 102 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 131 272 (Polychromatic418967fa.accept_20_1_11_12_1_2467 101
  131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 131 272 (accept_3_2 100
  131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 131 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 99 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 98 131 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 98 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 131 272 (accept_3_2 97 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 96 131 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 96 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 131 272 (Polychromatic418967fa.accept_7_4_5_6_1_344
  95 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 131 272 (accept_3_2 94
  131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 93 131 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 93 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 92 131 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 92 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 131 272 (accept_3_2 91 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 90 131 272 (Polychromatic418967fa.accept_21_6_5_20_1_12265 90 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 131 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 89 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 131 272 (accept_3_2 88 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 131 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 86 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 131 272 (accept_3_2 85 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 84 131 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 84 131 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 131 272
  (Polychromatic418967fa.accept_10_3_1_2_1_521 83 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 131 272 (accept_3_2 82 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 131 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 80 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 131 272 (accept_3_2 79 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 131 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 78 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 131 272
  (Polychromatic418967fa.accept_21_14_5_20_1_12299 77 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 76 131 272 (accept_3_2 76 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 75 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 131 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 74 131 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 131 272 (accept_3_2 73 131 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 131 272
  (Polychromatic418967fa.accept_23_3_16_19_1_16684 72 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 131 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 71 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 131 272 (accept_3_2 70 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 69 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 131 272
  (Polychromatic418967fa.accept_19_11_17_6_1_7157 68 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 67 131 272 (accept_3_2 67 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 66 131 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 66 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 131 272 (Polychromatic418967fa.accept_15_5_11_2_1_1095 65 131
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 131 272 (accept_3_2 64 131
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 131 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 63 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 62 131 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 62 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 131 272 (accept_3_2 61 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 60 131 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 60 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 131 272 (Polychromatic418967fa.accept_10_9_1_2_1_522
  59 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 131 272 (accept_3_2 58
  131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 57 131 272
  (Polychromatic418967fa.accept_6_3_5_2_1_12 57 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 56 131 272 (Polychromatic418967fa.accept_10_6_1_2_1_874 56 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 131 272 (accept_3_2 55 131 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 54 131 272 (Polychromatic418967fa.accept_13_2_1_12_1_1326 54 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 131 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 53 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 131 272 (accept_3_2 52 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 131 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 50 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 131 272 (accept_3_2 49 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 131 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 48 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 131 272
  (Polychromatic418967fa.accept_13_8_1_12_1_762 47 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 131 272 (accept_3_2 46 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 131 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 44 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 131 272 (accept_3_2 43 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 131 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 42 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 131 272
  (Polychromatic418967fa.accept_13_2_1_12_1_1326 41 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 131 272 (accept_3_2 40 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 131 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 38 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 131 272 (accept_3_2 37 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 131 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 36 131 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 131 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 35 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 131 272 (accept_3_2 34 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 131 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 32 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 131 272 (accept_3_2 31 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 131 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 30 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 131 272
  (Polychromatic418967fa.accept_7_1_5_6_1_59 29 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 131 272 (accept_3_2 28 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 131 272 (Polychromatic418967fa.accept_9_8_5_2_1_422 26 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 131 272 (accept_3_2 25 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 131 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 24 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 131 272
  (Polychromatic418967fa.accept_10_3_1_2_1_521 23 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 131 272 (accept_3_2 22 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 131 272 (Polychromatic418967fa.accept_11_9_10_8_1_444 20 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 131 272 (accept_3_2 19 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 131 272 (Polychromatic418967fa.accept_7_4_5_6_1_344 18 131 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 131 272
  (Polychromatic418967fa.accept_9_8_5_2_1_422 17 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 131 272 (accept_3_2 16 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 131 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 14 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 131 272 (accept_3_2 13 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 12 131 272 (Polychromatic418967fa.accept_9_3_5_2_1_28 12 131 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 131 272
  (Polychromatic418967fa.accept_7_4_5_6_1_344 11 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 131 272 (accept_3_2 10 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 131 272 (Polychromatic418967fa.accept_7_1_5_6_1_59 8 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 131 272 (accept_3_2 7 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 131 272 (Polychromatic418967fa.accept_9_6_5_2_1_421 6 131 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 131 272
  (Polychromatic418967fa.accept_13_5_1_12_1_740 5 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 131 272 (accept_3_2 4 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  131 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 131 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 131 272 (Polychromatic418967fa.accept_12_2_11_8_1_504 2 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 131 272 (accept_3_2 1 131 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 131
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 130 272 (allA_of_3_0 130 130 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 129 272
  (allA_succ_of_accept 128 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 128 129 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 127 129 272 (accept_3_2 127 129 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 126 129 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 126 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 125 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 125 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 124 129 272 (accept_3_2 124 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  123 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 123 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 122 129 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 122 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 129 272 (accept_3_2 121 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 129 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 120 129
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 129 272 (accept_3_2 118 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 129 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 117 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 116 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 129 272 (accept_3_2 115 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 114 129 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 129 272 (accept_3_2 112 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 129 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 111 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 129 272 (Polychromatic418967fa.accept_23_18_14_19_1_3436 110 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 129 272 (accept_3_2 109 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 129 272 (Polychromatic418967fa.accept_14_10_3_6_1_2728 108
  129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 129 272 (accept_3_2 106 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 105 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 129 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 104 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 129 272 (accept_3_2 103 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 102 129
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 129 272 (accept_3_2 100 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 129 272 (Polychromatic418967fa.accept_18_9_3_2_1_3814 99 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 98 129 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 98 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 129 272 (accept_3_2 97 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 96 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 96 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 129 272 (accept_3_2 94 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 93 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 129 272 (Polychromatic418967fa.accept_19_16_15_6_1_12661 92 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 129 272 (accept_3_2 91 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 129 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 90 129
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 129 272 (accept_3_2 88 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 87 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 86 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 129 272 (accept_3_2 85 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 129 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 84 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 129 272 (accept_3_2 82 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 81 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 129 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 80 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 129 272 (accept_3_2 79 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 78 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 129 272 (accept_3_2 76 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 129 272 (Polychromatic418967fa.accept_21_12_3_20_1_4567 75 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 74 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 129 272 (accept_3_2 73 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 72 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 72 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 129 272 (accept_3_2 70 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 69 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 129 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 68 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 129 272 (accept_3_2 67 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 129 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 66 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 129 272 (accept_3_2 64 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 129 272 (Polychromatic418967fa.accept_18_9_3_2_1_3814 63 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 129 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 62 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 129 272 (accept_3_2 61 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 60 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 129 272 (accept_3_2 58 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 129 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 57 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 129 272 (Polychromatic418967fa.accept_15_11_9_2_1_4780 56 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 129 272 (accept_3_2 55 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 129 272 (Polychromatic418967fa.accept_12_6_9_8_1_165 54 129
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 129 272 (accept_3_2 52 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 51 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 129 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 50 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 129 272 (accept_3_2 49 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 129 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 48 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 129 272 (accept_3_2 46 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 129 272 (Polychromatic418967fa.accept_18_9_3_2_1_3814 45 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 44 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 129 272 (accept_3_2 43 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 42 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 129 272 (accept_3_2 40 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 39 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 129 272 (Polychromatic418967fa.accept_14_10_3_6_1_2728 38 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 129 272 (accept_3_2 37 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 36 129 272 (Polychromatic418967fa.accept_27_9_21_2_1_16683 36 129
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 129 272 (accept_3_2 34 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 33 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 32 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 129 272 (accept_3_2 31 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 30 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 129 272 (accept_3_2 28 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 129 272 (Polychromatic418967fa.accept_10_7_9_2_1_1887 27 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 129 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 26 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 129 272 (accept_3_2 25 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 24 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 129 272 (accept_3_2 22 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 129 272 (Polychromatic418967fa.accept_10_1_9_2_1_45 21 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 129 272 (Polychromatic418967fa.accept_22_20_19_8_1_9003 20 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 129 272 (accept_3_2 19 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 129 272 (Polychromatic418967fa.accept_7_4_3_6_1_340 18 129 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 129 272 (accept_3_2 16 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 15 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 129 272 (Polychromatic418967fa.accept_9_5_3_2_1_171 14 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 129 272 (accept_3_2 13 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 129 272 (Polychromatic418967fa.accept_18_12_3_2_1_756 12 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 129 272 (accept_3_2 10 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 9 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 129 272 (Polychromatic418967fa.accept_9_8_3_2_1_417 8 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 129 272 (accept_3_2 7 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 129 272 (Polychromatic418967fa.accept_9_6_3_2_1_431 6 129 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 129 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 129 272 (accept_3_2 4 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  129 272 (Polychromatic418967fa.accept_20_3_9_12_1_6671 3 129 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 129 272 (Polychromatic418967fa.accept_7_2_3_6_1_4 2 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 129 272 (accept_3_2 1 129 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 129
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 128 272 (allA_succ_of_accept 127 128 272 (accept_3_2 127 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 126 128 272 2 63 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 125 128 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 125 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 128 272 4 31 32 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 128 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 123 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 128 272 2 61 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 128 272 (accept_3_2 121 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 128 272 8 15 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 128 272 (Polychromatic418967fa.accept_19_5_14_6_1_4413 119 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 128 272 2 59 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 128 272
  (Polychromatic418967fa.accept_22_7_18_8_1_13589 117 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 116 128 272 4 29 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 115 128 272 (accept_3_2 115 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 128 272 2 57 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 128 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 113 128 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 128 272 16 7 8 17 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 128 272
  (Polychromatic418967fa.accept_13_7_11_12_1_2051 111 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 110 128 272 2 55 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 109 128 272 (accept_3_2 109 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 128 272 4 27 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 128 272 (Polychromatic418967fa.accept_19_12_14_6_1_12670 107 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 128 272 2 53 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 128 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 105 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 128 272 8 13 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 128 272 (accept_3_2 103 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 128 272 2 51 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 128 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 101 128 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 128 272 4 25 32 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 128 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 99 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 128 272 2 49 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 128 272 (accept_3_2 97 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 128 272 16 6 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 95 128 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 95 128 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 128 272 2 47 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 128 272 (Polychromatic418967fa.accept_21_9_2_20_1_857
  93 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 92 128 272 4 23 32 68
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 91 128 272
  (accept_3_2 91 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 90 128 272 2 45 64 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 89 128 272
  (Polychromatic418967fa.accept_21_5_2_20_1_6081 89 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 88 128 272 8 11 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 87 128 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 87 128 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 86 128 272 2 43 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 85 128 272 (accept_3_2 85 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 84 128 272 4 21 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 83 128 272 (Polychromatic418967fa.accept_19_7_14_6_1_9987
  83 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 128 272 2 41 64 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 128 272
  (Polychromatic418967fa.accept_7_4_2_6_1_337 81 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 128 272 16 5 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 79 128 272 (accept_3_2 79 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 78
  128 272 2 39 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 77 128 272 (Polychromatic418967fa.accept_19_1_14_6_1_1983 77 128 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 128 272 4 19 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 128 272 (Polychromatic418967fa.accept_10_5_8_2_1_517
  75 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 74 128 272 2 37 64 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 73 128 272
  (accept_3_2 73 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 72 128 272 8 9 16 34 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 71 128 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 71 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 70 128 272 2 35 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 69 128 272 (Polychromatic418967fa.accept_13_4_11_12_1_1318 69 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 68 128 272 4 17 32 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 67 128 272 (accept_3_2 67 128 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 66 128 272 2 33 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 65 128 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 65 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 64 128 272 16 4 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 63 128 272 (Polychromatic418967fa.accept_22_19_18_8_1_8915 63 128 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 62 128 272 2 31 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 61 128 272 (accept_3_2 61 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 60 128 272 4 15 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 59 128 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 59
  128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 128 272 2 29 64 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 128 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 57 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 128 272 8 7 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 55 128 272 (accept_3_2 55 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 54
  128 272 2 27 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 53 128 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 53 128 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 128 272 4 13 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 128 272 (Polychromatic418967fa.accept_15_6_8_2_1_104
  51 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 50 128 272 2 25 64 136
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 49 128 272
  (accept_3_2 49 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 48 128 272 16 3 8 17 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 47 128 272
  (Polychromatic418967fa.accept_19_9_14_6_1_2014 47 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 46 128 272 2 23 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 45 128 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 45 128 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 44 128 272 4 11 32 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 43 128 272 (accept_3_2 43 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 42 128 272 2 21 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 41 128 272
  (Polychromatic418967fa.accept_22_19_18_8_1_8915 41 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 40 128 272 8 5 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 39 128 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 39 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 38 128 272 2 19 64 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 37 128 272 (accept_3_2 37 128 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 36 128 272 4 9 32 68 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 35 128 272
  (Polychromatic418967fa.accept_10_5_8_2_1_517 35 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 34 128 272 2 17 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 33 128 272 (Polychromatic418967fa.accept_13_7_11_12_1_2051 33 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 32 128 272 16 2 8 17 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 31 128 272 (accept_3_2 31 128 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 30 128 272 2 15 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 29 128 272
  (Polychromatic418967fa.accept_7_1_2_6_1_55 29 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 28 128 272 4 7 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 27 128 272 (Polychromatic418967fa.accept_13_1_11_12_1_1322 27 128 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 26 128 272 2 13 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 25 128 272 (accept_3_2 25 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 24 128 272 8 3 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 23 128 272
  (Polychromatic418967fa.accept_13_10_11_12_1_1320 23 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 22 128 272 2 11 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 21 128 272 (Polychromatic418967fa.accept_15_6_8_2_1_104 21 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 20 128 272 4 5 32 68 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 19 128 272 (accept_3_2 19 128 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 18 128 272 2 9 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 17 128 272
  (Polychromatic418967fa.accept_7_3_2_6_1_56 17 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 16 128 272 16 1 8 17 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 15 128 272 (Polychromatic418967fa.accept_7_1_2_6_1_55 15 128 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 14 128 272 2 7 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 13 128 272 (accept_3_2 13 128 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_gcd 12 128 272 4 3 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 11 128 272 (Polychromatic418967fa.accept_7_4_2_6_1_337 11 128 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 128 272 2 5 64 136 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 128 272
  (Polychromatic418967fa.accept_15_9_8_2_1_1109 9 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 128 272 8 1 16 34 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 128 272 (accept_3_2 7 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 128
  272 2 3 64 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  128 272 (Polychromatic418967fa.accept_10_5_8_2_1_517 5 128 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 128 272 4 1 32 68 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 3 128 272 (Polychromatic418967fa.accept_7_3_2_6_1_56 3 128 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 128 272 2 1 64 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 128 272 (accept_3_2 1 128 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_one 128
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 127 272 (allA_of_3_0 127 127 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 126 272
  (allA_succ_of_accept 125 126 272 (Polychromatic418967fa.accept_13_8_9_12_1_2813 125 126 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 124 126 272 2 62 63 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 123 126 272
  (Polychromatic418967fa.accept_11_2_5_8_1_470 123 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 122 126 272 2 61 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 121 126 272 (accept_3_2 121 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 120 126 272 2 60 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 119 126 272 (Polychromatic418967fa.accept_22_9_16_8_1_4058 119 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 118 126 272 2 59 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 117 126 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 117 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 116 126 272 2 58 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 115 126 272 (accept_3_2 115 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 114 126 272 2 57 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 113 126 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 113 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 112 126 272 2 56 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 111 126 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 111 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 110 126 272 2 55 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 109 126 272 (accept_3_2 109 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 108 126 272 2 54 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 107 126 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062 107 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 106 126 272 2 53 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 105 126 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 105 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 104 126 272 2 52 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 103 126 272 (accept_3_2 103 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 102 126 272 2 51 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 101 126 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 101 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 100 126 272 2 50 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 99 126 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 99 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 98 126 272 2 49 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 97 126 272 (accept_3_2 97 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 96 126 272 2 48 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 95 126 272 (Polychromatic418967fa.accept_20_15_6_12_1_2446 95 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 94 126 272 2 47 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 93 126 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 93 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 92 126 272 2 46 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 91 126 272 (accept_3_2 91 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 90 126 272 2 45 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 89 126 272 (Polychromatic418967fa.accept_19_13_12_6_1_11362 89 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 88 126 272 2 44 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 87 126 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 87 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 86 126 272 2 43 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 85 126 272 (accept_3_2 85 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 84 126 272 2 42 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 83 126 272 (Polychromatic418967fa.accept_15_8_6_2_1_1128 83 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 82 126 272 2 41 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 81 126 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 81 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 80 126 272 2 40 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 79 126 272 (accept_3_2 79 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 78 126 272 2 39 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 77 126 272 (Polychromatic418967fa.accept_20_17_6_12_1_8185 77 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 76 126 272 2 38 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 75 126 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 75 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 74 126 272 2 37 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 73 126 272 (accept_3_2 73 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 72 126 272 2 36 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 71 126 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 71 126 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 70 126 272 2 35 63 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 69 126 272
  (Polychromatic418967fa.accept_11_3_5_8_1_458 69 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 68 126 272 2 34 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 67 126 272 (accept_3_2 67 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 66 126 272 2 33 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 65 126 272 (Polychromatic418967fa.accept_19_8_12_6_1_1976 65 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 64 126 272 2 32 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 63 126 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 63 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 62 126 272 2 31 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 61 126 272 (accept_3_2 61 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 60 126 272 2 30 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 59 126 272 (Polychromatic418967fa.accept_19_2_12_6_1_5816 59 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 58 126 272 2 29 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 57 126 272
  (Polychromatic418967fa.accept_11_2_5_8_1_470 57 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 56 126 272 2 28 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 55 126 272 (accept_3_2 55 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 54 126 272 2 27 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 53 126 272 (Polychromatic418967fa.accept_15_8_6_2_1_1128 53 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 52 126 272 2 26 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 51 126 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 51 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 50 126 272 2 25 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 49 126 272 (accept_3_2 49 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 48 126 272 2 24 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 47 126 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 47 126 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 46 126 272 2 23 63 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 45 126 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 45 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 44 126 272 2 22 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 43 126 272 (accept_3_2 43 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 42 126 272 2 21 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 41 126 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 41 126 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 40 126 272 2 20 63 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 39 126 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 39 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 38 126 272 2 19 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 37 126 272 (accept_3_2 37 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 36 126 272 2 18 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 35 126 272 (Polychromatic418967fa.accept_11_2_5_8_1_470 35 126 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 34 126 272 2 17 63 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 33 126 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 33 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 32 126 272 2 16 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 31 126 272 (accept_3_2 31 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 30 126 272 2 15 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 29 126 272 (Polychromatic418967fa.accept_13_3_9_12_1_2062 29 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 28 126 272 2 14 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 27 126 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 27 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 26 126 272 2 13 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 25 126 272 (accept_3_2 25 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 24 126 272 2 12 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 23 126 272 (Polychromatic418967fa.accept_13_10_9_12_1_2814 23 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 22 126 272 2 11 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 21 126 272
  (Polychromatic418967fa.accept_10_1_6_2_1_867 21 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 20 126 272 2 10 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 19 126 272 (accept_3_2 19 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 18 126 272 2 9 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 17 126 272 (Polychromatic418967fa.accept_19_17_12_6_1_8650 17 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 16 126 272 2 8 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 15 126 272
  (Polychromatic418967fa.accept_12_3_6_8_1_969 15 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 14 126 272 2 7 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 13 126 272 (accept_3_2 13 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 12 126 272 2 6 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true) (allA_succ_of_accept 11 126 272 (Polychromatic418967fa.accept_10_1_6_2_1_867 11 126 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 10 126 272 2 5 63 136 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 9 126 272
  (Polychromatic418967fa.accept_12_9_6_8_1_518 9 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_gcd 8 126 272 2 4 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (allA_succ_of_accept 7 126 272 (accept_3_2 7 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 6 126
  272 2 3 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 5
  126 272 (Polychromatic418967fa.accept_20_5_6_12_1_2444 5 126 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_gcd 4 126 272 2 2 63 136 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true) (allA_succ_of_accept 3 126 272 (Polychromatic418967fa.accept_11_3_5_8_1_458 3 126 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_gcd 2 126 272 2 1 63 136 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true) (allA_succ_of_accept 1 126 272 (accept_3_2 1 126 272
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 126
  272))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 125 272 (allA_succ_of_accept 124 125 272 (accept_3_2 124 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 123 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 123 125 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 122 125 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 122 125
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 125 272 (accept_3_2 121 125
  272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 120 125 272
  (Polychromatic418967fa.accept_9_3_8_2_1_162 120 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 119 125 272 (Polychromatic418967fa.accept_14_7_13_6_1_1177 119 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 118 125 272 (accept_3_2 118 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 117 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 117 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 116 125 272
  (Polychromatic418967fa.accept_15_11_5_2_1_520 116 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 115 125 272 (accept_3_2 115 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  114 125 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 114 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 113 125 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 113 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 112 125 272 (accept_3_2 112 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 111 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 111 125
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 110 125 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 110 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 109 125 272 (accept_3_2 109 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  108 125 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 108 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 107 125 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 107 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 106 125 272 (accept_3_2 106 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 105 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 105 125
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 104 125 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 104 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 103 125 272 (accept_3_2 103 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  102 125 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 102 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 101 125 272 (Polychromatic418967fa.accept_13_10_8_12_1_2032 101 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 100 125 272 (accept_3_2 100 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 99 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 99 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 98 125 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 98 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 97 125 272 (accept_3_2 97 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  96 125 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 96 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 95 125 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 95 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 94 125 272 (accept_3_2 94 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 93 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 93 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 92 125 272
  (Polychromatic418967fa.accept_13_1_8_12_1_2045 92 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 91 125 272 (accept_3_2 91 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  90 125 272 (Polychromatic418967fa.accept_19_14_11_6_1_7151 90 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 89 125 272 (Polychromatic418967fa.accept_11_1_4_8_1_1918 89 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 88 125 272 (accept_3_2 88 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 87 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 87 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 86 125 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 86 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 85 125 272 (accept_3_2 85 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  84 125 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 84 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 83 125 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 83 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 82 125 272 (accept_3_2 82 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 81 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 81 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 80 125 272
  (Polychromatic418967fa.accept_18_8_17_2_1_1557 80 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 79 125 272 (accept_3_2 79 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  78 125 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 78 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 77 125 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 77 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 76 125 272 (accept_3_2 76 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 75 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 75 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 74 125 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 74 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 73 125 272 (accept_3_2 73 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  72 125 272 (Polychromatic418967fa.accept_13_7_8_12_1_2810 72 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 71 125 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 71 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 70 125 272 (accept_3_2 70 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 69 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 69 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 68 125 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 68 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 67 125 272 (accept_3_2 67 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  66 125 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 66 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 65 125 272 (Polychromatic418967fa.accept_18_11_17_2_1_6349 65 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 64 125 272 (accept_3_2 64 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 63 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 63 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 62 125 272
  (Polychromatic418967fa.accept_11_7_4_8_1_1371 62 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 61 125 272 (accept_3_2 61 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  60 125 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 60 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 59 125 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 59 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 58 125 272 (accept_3_2 58 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 57 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 57 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 56 125 272
  (Polychromatic418967fa.accept_11_1_4_8_1_1918 56 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 55 125 272 (accept_3_2 55 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  54 125 272 (Polychromatic418967fa.accept_14_12_13_6_1_1140 54 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 53 125 272 (Polychromatic418967fa.accept_10_3_5_2_1_38 53 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 52 125 272 (accept_3_2 52 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 51 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 51 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 50 125 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 50 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 49 125 272 (accept_3_2 49 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  48 125 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 48 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 47 125 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 47 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 46 125 272 (accept_3_2 46 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 45 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 45 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 44 125 272
  (Polychromatic418967fa.accept_13_5_8_12_1_2759 44 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 43 125 272 (accept_3_2 43 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  42 125 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 42 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 41 125 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 41 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 40 125 272 (accept_3_2 40 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 39 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 39 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 38 125 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 38 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 37 125 272 (accept_3_2 37 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  36 125 272 (Polychromatic418967fa.accept_13_10_8_12_1_2032 36 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 35 125 272 (Polychromatic418967fa.accept_13_9_8_12_1_2031 35 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 34 125 272 (accept_3_2 34 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 33 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 33 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 32 125 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 32 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 31 125 272 (accept_3_2 31 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  30 125 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 30 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 29 125 272 (Polychromatic418967fa.accept_11_7_4_8_1_1371 29 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 28 125 272 (accept_3_2 28 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 27 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 27 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 26 125 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 26 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 25 125 272 (accept_3_2 25 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  24 125 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 24 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 23 125 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 23 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 22 125 272 (accept_3_2 22 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 21 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 21 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 20 125 272
  (Polychromatic418967fa.accept_13_7_8_12_1_2810 20 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 19 125 272 (accept_3_2 19 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  18 125 272 (Polychromatic418967fa.accept_10_8_5_2_1_881 18 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 17 125 272 (Polychromatic418967fa.accept_10_7_5_2_1_880 17 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 16 125 272 (accept_3_2 16 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 15 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 15 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 14 125 272
  (Polychromatic418967fa.accept_9_5_8_2_1_409 14 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 13 125 272 (accept_3_2 13 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  12 125 272 (Polychromatic418967fa.accept_9_3_8_2_1_162 12 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 11 125 272 (Polychromatic418967fa.accept_15_11_5_2_1_520 11 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 10 125 272 (accept_3_2 10 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 9 125 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 8 125 272
  (Polychromatic418967fa.accept_10_8_5_2_1_881 8 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 7 125 272 (accept_3_2 7 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 6
  125 272 (Polychromatic418967fa.accept_9_6_8_2_1_410 6 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 5 125 272 (Polychromatic418967fa.accept_9_5_8_2_1_409 5 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 4 125 272 (accept_3_2 4 125 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 3 125 272 (Polychromatic418967fa.accept_6_3_5_2_1_12 3 125 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 2 125 272
  (Polychromatic418967fa.accept_12_2_5_8_1_159 2 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 1 125 272 (accept_3_2 1 125 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_one 125
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (allB_succ 124 272 (allA_of_3_0 124 124 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allB_succ 123 272
  (allA_succ_of_accept 122 123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 122 123 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 121 123 272 (accept_3_2 121 123 272 (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 120 123 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 120 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 119 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 119 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 118 123 272 (accept_3_2 118 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  117 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 117 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 116 123 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 116 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 115 123 272 (accept_3_2 115 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 114 123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 114 123
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 113 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 113 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 112 123 272 (accept_3_2 112 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  111 123 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 111 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 110 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 110 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 109 123 272 (accept_3_2 109 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 108 123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 108 123
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 107 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 107 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 106 123 272 (accept_3_2 106 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  105 123 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 105 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 104 123 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 104 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 103 123 272 (accept_3_2 103 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 102 123 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 102 123
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 101 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 101 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 100 123 272 (accept_3_2 100 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  99 123 272 (Polychromatic418967fa.accept_21_15_18_20_1_9292 99 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 98 123 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 98 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 97 123 272 (accept_3_2 97 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 96 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 96 123 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 95 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 95 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 94 123 272 (accept_3_2 94 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  93 123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 93 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 92 123 272 (Polychromatic418967fa.accept_19_16_9_6_1_5799 92 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 91 123 272 (accept_3_2 91 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 90 123 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 90 123
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 89 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 89 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 88 123 272 (accept_3_2 88 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  87 123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 87 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 86 123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 86 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 85 123 272 (accept_3_2 85 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 84 123 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 84 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 83 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 83 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 82 123 272 (accept_3_2 82 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  81 123 272 (Polychromatic418967fa.accept_10_1_3_2_1_220 81 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 80 123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 80 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 79 123 272 (accept_3_2 79 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 78 123 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 78 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 77 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 77 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 76 123 272 (accept_3_2 76 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  75 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 75 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 74 123 272 (Polychromatic418967fa.accept_15_14_3_2_1_2811 74 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 73 123 272 (accept_3_2 73 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 72 123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 72 123 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 71 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 71 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 70 123 272 (accept_3_2 70 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  69 123 272 (Polychromatic418967fa.accept_20_9_3_12_1_6627 69 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 68 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 68 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 67 123 272 (accept_3_2 67 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 66 123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 66 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 65 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 65 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 64 123 272 (accept_3_2 64 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  63 123 272 (Polychromatic418967fa.accept_27_9_15_2_1_11080 63 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 62 123 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 62 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 61 123 272 (accept_3_2 61 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 60 123 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 60 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 59 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 59 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 58 123 272 (accept_3_2 58 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  57 123 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 57 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 56 123 272 (Polychromatic418967fa.accept_19_18_9_6_1_5815 56 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 55 123 272 (accept_3_2 55 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 54 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 54 123 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 53 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 53 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 52 123 272 (accept_3_2 52 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  51 123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 51 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 50 123 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 50 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 49 123 272 (accept_3_2 49 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 48 123 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 48 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 47 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 47 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 46 123 272 (accept_3_2 46 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  45 123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 45 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 44 123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 44 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 43 123 272 (accept_3_2 43 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 42 123 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 42 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 41 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 41 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 40 123 272 (accept_3_2 40 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  39 123 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 39 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 38 123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 38 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 37 123 272 (accept_3_2 37 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 36 123 272 (Polychromatic418967fa.accept_13_10_6_12_1_2780 36 123 272
  (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 35 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 35 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 34 123 272 (accept_3_2 34 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  33 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 33 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 32 123 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 32 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 31 123 272 (accept_3_2 31 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 30 123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 30 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 29 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 29 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 28 123 272 (accept_3_2 28 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  27 123 272 (Polychromatic418967fa.accept_11_5_2_8_1_866 27 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 26 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 26 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 25 123 272 (accept_3_2 25 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 24 123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 24 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 23 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 23 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 22 123 272 (accept_3_2 22 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  21 123 272 (Polychromatic418967fa.accept_9_3_6_2_1_160 21 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 20 123 272 (Polychromatic418967fa.accept_13_7_6_12_1_2027 20 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 19 123 272 (accept_3_2 19 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 18 123 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 18 123
  272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 17 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 17 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 16 123 272 (accept_3_2 16 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept
  15 123 272 (Polychromatic418967fa.accept_10_5_3_2_1_899 15 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 14 123 272 (Polychromatic418967fa.accept_9_5_6_2_1_161 14 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 13 123 272 (accept_3_2 13 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 12 123 272 (Polychromatic418967fa.accept_7_5_4_6_1_167 12 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 11 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 11 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 10 123 272 (accept_3_2 10 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 9
  123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 9 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 8 123 272 (Polychromatic418967fa.accept_9_8_6_2_1_744 8 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 7 123 272 (accept_3_2 7 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_succ_of_accept 6 123 272 (Polychromatic418967fa.accept_12_6_3_8_1_512 6 123 272 (Eq.refl
  Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 5 123 272
  (Polychromatic418967fa.accept_6_5_3_2_1_68 5 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl Bool.true))
  (allA_succ_of_accept 4 123 272 (accept_3_2 4 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 3
  123 272 (Polychromatic418967fa.accept_7_3_4_6_1_329 3 123 272 (Eq.refl Bool.true) (Eq.refl Bool.true) (Eq.refl
  Bool.true)) (allA_succ_of_accept 2 123 272 (Polychromatic418967fa.accept_7_2_4_6_1_166 2 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true) (Eq.refl Bool.true)) (allA_succ_of_accept 1 123 272 (accept_3_2 1 123 272 (Eq.refl Bool.true)
  (Eq.refl Bool.true)) (allA_one 123
  272)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Polychromatic418967fa.branch_272_segment_000)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


